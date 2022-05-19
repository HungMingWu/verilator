#include <fstream>
#include <string>
#include "V3Ast.h"
#include "V3ClockExtract.h"
#include "V3EmitCBase.h"
#include "V3OrderGraph.h"
#include "V3AstUserAllocator.h"
#include "partition/V3EmitV.h"
#include "partition/V3Utils.h"

namespace Clock {

class MoveOutActiveModule : public VNVisitor
{
    virtual void visit(AstActive* nodep) override
    {
        nodep->unlinkFrBack();
        m_acitves.push_back(nodep);
    }
    virtual void visit(AstNode* nodep) override { iterateChildrenConst(nodep); }
public:
    std::vector<AstActive*> m_acitves;
    MoveOutActiveModule(AstNodeModule* nodep) {
        iterate(nodep);
    }
};

class MoveAssignDly : public VNVisitor
{
    AstNodeModule* to;
    AstActive* clone_activep = nullptr;
    size_t color;
    virtual void visit(AstAssignDly* nodep) override {
        printf("visit AstAssignDly %p color is %d\n", nodep, nodep->user1());
        if (nodep->user1() != color) { nodep->unlinkFrBack(); }
    }
    virtual void visit(AstNode* nodep) override { iterateChildrenConst(nodep); }
public:
    MoveAssignDly(std::vector<AstActive*> actives, AstNodeModule* to_, size_t color_)
        : to(to_)
        , color(color_) {
        for (auto& activep : actives) {
            AstActive* clone_activep = activep->cloneTree(true);
            iterate(clone_activep);
            to->addStmtp(clone_activep);
        }
    }
};

class DivideGraph : public VNVisitor {
    V3Graph m_graph;
    AstAssignDly* m_curDly = nullptr;
    AstNodeModule* m_modp = nullptr;
    AstNodeModule* m_restMod = nullptr;
    std::map<V3GraphVertex*, AstAssignDly*> m_delayMappings;
    std::vector<AstNodeModule*> part_modules;
    std::unordered_map<AstNode *, V3GraphVertex*> existed_vertex;
    V3GraphVertex* find(AstNode *nodep) {
        auto it = existed_vertex.find(nodep);
        if (it != existed_vertex.end()) { return it->second; }
        auto vertex = new V3GraphVertex(&m_graph);
        printf("create a new graph vertex %p,\n", vertex);
        existed_vertex[nodep] = vertex;
        return vertex;
    }

    virtual void visit(AstAlways* nodep) override {
        printf("begin AstAlways\n");
        iterateChildrenConst(nodep);
        printf("end AstAlways\n");
    }
    virtual void visit(AstNot *nodep) {
        printf("begin AstNot\n");
        if (m_curDly) {
            V3GraphVertex* from = find(m_curDly);
            V3GraphVertex* to = find(nodep);
            new V3GraphEdge(&m_graph, from, to, 1);
            new V3GraphEdge(&m_graph, to, from, 1);
            printf("Append an edge from %p to %p\n", m_curDly, nodep);
        }
        printf("end AstNot\n");
    }

    virtual void visit(AstAnd* nodep) {
        printf("begin AstAnd\n");
        if (m_curDly) {
            V3GraphVertex* from = find(m_curDly);
            V3GraphVertex* to = find(nodep);
            new V3GraphEdge(&m_graph, from, to, 1);
            new V3GraphEdge(&m_graph, to, from, 1);
            printf("Append an edge from %p to %p\n", m_curDly, nodep);
        }
        printf("end AstAnd\n");
    }

    virtual void visit(AstActive* nodep) override {
        printf("begin active sensep = %p\n", nodep->sensesp());
        iterateChildrenConst(nodep);
        printf("end active\n");
    }
    virtual void visit(AstAssignDly* nodep) override {
        printf("begin assigndly %p\n", nodep);
        VL_RESTORER(m_curDly);
        m_curDly = nodep;
        V3GraphVertex* vertex = find(nodep);
        m_delayMappings[vertex] = nodep;
        iterateChildrenConst(nodep);
        printf("end assigndly\n");
    }
    virtual void visit(AstNode* nodep) override { iterateChildrenConst(nodep); }

public:
    DivideGraph(AstNodeModule* nodep) {
        m_restMod = nodep->cloneTree(true);
        printf("Start process\n");
        iterate(m_restMod);
        printf("End process\n");
        pushDeletep(m_restMod);
    }
    void process() {
        m_graph.stronglyConnected(V3GraphEdge::followAlwaysTrue);
        printf("Begin colors\n");
        for (V3GraphVertex* vertexp = m_graph.verticesBeginp(); vertexp;
             vertexp = vertexp->verticesNextp()) {
            printf("Vertex %p color %d\n", vertexp, vertexp->color());
        }
        printf("End colors\n");

        // build strongly connected contract graph
        uint32_t index = 0;
        std::unordered_map<uint32_t, uint32_t> color_map;
        for (V3GraphVertex* vertexp = m_graph.verticesBeginp(); vertexp;
             vertexp = vertexp->verticesNextp()) {
            auto it = color_map.find(vertexp->color());
            if (it == color_map.end()) {
                printf("create a new mapping, %u -> %u\n", vertexp->color(), index);
                color_map[vertexp->color()] = index++;
            }
        }
        size_t total_partitions = 3;
        size_t parts[3] = {1, 1, 0};
        for (V3GraphVertex* fromp = m_graph.verticesBeginp(); fromp;
             fromp = fromp->verticesNextp()) 
        {
            auto it = m_delayMappings.find(fromp);
            if (it != m_delayMappings.end()) { 
                printf("fromp %p assign dly %p to color %d\n", fromp, it->second, color_map[fromp->color()]);
                it->second->user1(parts[color_map[fromp->color()]]);
            }
            #if 0
            for (V3GraphEdge* edgep = fromp->outBeginp(); edgep; edgep = edgep->outNextp()) {
                V3GraphVertex* top = edgep->top();

                if (fromp->color() == top->color()) {

                    printf("%p -> %p have same color\n", fromp, top);
                    continue;
                } else {
                    printf("%p -> %p have different color\n", fromp, top);
                }
            }
            #endif
        }
        // Simulate Rest__x

        MoveOutActiveModule activeVisitor(m_restMod);
        for (size_t part = 0; part < 2; part++) part_modules.push_back(m_restMod->cloneTree(true));
        for (size_t part = 0; part < 2; part++) {

            MoveAssignDly visitor(activeVisitor.m_acitves, part_modules[part], part);
            std::string name = "part__" + std::to_string(part);
            auto cell_in_rest = new AstCell(nullptr, nullptr, name, name,
                                              nullptr, nullptr, nullptr);
            m_restMod->addStmtp(cell_in_rest);
        }
#if 1
    printf("begin print m_modp\n");
    partition::verilogForTree(m_restMod);
    printf("end print m_modp\n");

    for (auto& part : part_modules)
    {
        printf("begin print rest_modules\n");
        partition::verilogForTree(part);
        printf("end print rest_modules\n");
    }

#endif
    }
};
}  // namespace Clock

class RemoveVarVisitor final : public VNVisitor 
{
    std::string m_target_name;
    AstVar* m_newtarget_in;
    AstVar* m_newtarget_out;
    virtual void visit(AstVarRef* nodep) 
    { 
        if (nodep->varp() && nodep->varp()->name() == m_target_name)
        { 
            printf("found target, change it\n");
            nodep->varp(m_newtarget_out);
        }
    }
    virtual void visit(AstSenItem* nodep) {
        printf("begin sen item\n");
        AstNodeVarRef* varrefp = nodep->varrefp();
        if (varrefp && varrefp->varp() && varrefp->varp()->name() == m_target_name) {
            printf("found target, change it\n");
            varrefp->varp(m_newtarget_in);
        }
        printf("end sen item\n");
    }
    // Default
    virtual void visit(AstNode* nodep) override 
    { 
        iterateChildrenConst(nodep);
    }

public:
    RemoveVarVisitor(AstNodeModule* nodep, std::string target_name, AstVar* newtarget_in,
                     AstVar* newtarget_out)
        : m_target_name(target_name)
        , m_newtarget_in(newtarget_in)
        , m_newtarget_out(newtarget_out)
    {
        iterate(nodep);
    }
};
class ClockExtractVisitor final : public VNVisitor {
    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    // VISITORS
    virtual void visit(AstNodeModule* nodep) override {
        if (!m_new_dut_modp) {
            m_new_dut_modp = nodep->cloneTree(true);
            m_modp = new AstModule(nullptr, "dut", false);
            partition::CollectPort c(m_new_dut_modp);
            for (auto& var : c.m_vars) m_modp->addStmtp(var->cloneTree(false));
            iterateChildren(nodep);
            pushDeletep(m_modp);
            pushDeletep(m_new_dut_modp);
        }
    }

    virtual void visit(AstAssignDly* nodep) override {
        const AstVarRef* const lhsp = VN_AS(nodep->lhsp(), VarRef);
        AstVar* var = lhsp->varp();
        if (var->isUsedClock()) {  // nodep->direction() == VDirection::INPUT) {
            printf("push var %p name %s, origname = %s, isUsedClock = %d\n", var,
                   var->name().c_str(), var->origName().c_str(), var->isUsedClock());
            m_divided_clocks.push_back(var);
        }
    }

    //--------------------
    virtual void visit(AstNode* nodep) override { iterateChildren(nodep); }
    void build_clocktree();
public:
    // CONSTRUCTORS
    explicit ClockExtractVisitor(AstNetlist* nodep) { iterate(nodep); }
    virtual ~ClockExtractVisitor() override = default;

    // STATE
    AstNodeModule* m_modp = nullptr;
    AstNodeModule* m_new_dut_modp = nullptr;
    // Clocks
    std::vector<AstVar*> m_divided_clocks;
    void build();
};

inline void append_pin_in_list(AstPin*& last, AstPin* newpin) {
    if (last == nullptr)
        last = newpin;
    else
        last = static_cast<AstPin*>(last->addNext(newpin));
}

void ClockExtractVisitor::build_clocktree() 
{
    std::ofstream clockTree("gen__ClockTree.sv");
    std::string module_name = "ClockTree";
    auto clktree_module = new AstModule(nullptr, module_name, false);
    int count = 0;
    AstPin* pin_in_newdut = nullptr;
    partition::CollectPort c(m_new_dut_modp);
    for (auto& var : c.m_vars) {
        append_pin_in_list(pin_in_newdut, new AstPin(nullptr, 0, var->name(), var->cloneTree(false)));
    }
    AstPin* pin_in_clocktree = nullptr;
    for (auto& var : m_divided_clocks) {
        std::string in_var_name = var->name() + "_i";
        std::string out_var_name = var->name() + "_o";
        std::string top_in_var_name = var->name() + "_fromNewDut";
        std::string top_out_var_name = var->name() + "_toNewDut";
        auto var_inport = new AstPort{nullptr, count++, in_var_name};
        auto var_outport = new AstPort{nullptr, count++, out_var_name};
        clktree_module->addStmtp(var_inport);
        clktree_module->addStmtp(var_outport);
        printf("divided_clocks %p, name is %s\n", var, var->name().c_str());
        auto invar = new AstVar(nullptr, var->varType(), in_var_name, var->dtypep());
        invar->direction(VDirection::INPUT);
        auto outvar = new AstVar(nullptr, var->varType(), out_var_name, var->dtypep());
        outvar->direction(VDirection::OUTPUT);
        auto top_in_var_in_cell = new AstVar(nullptr, var->varType(), top_in_var_name, var->dtypep());
        auto top_in_var = new AstVar(nullptr, var->varType(), top_in_var_name, var->dtypep());
        auto top_out_var_in_cell = new AstVar(nullptr, var->varType(), top_out_var_name, var->dtypep());
        auto top_out_var = new AstVar(nullptr, var->varType(), top_out_var_name, var->dtypep());
        auto invarref = new AstVarRef(nullptr, invar, VAccess::READ);
        auto outvarref = new AstVarRef(nullptr, outvar, VAccess::WRITE);
        auto assign = new AstAssignW(nullptr, outvarref, invarref);
        m_modp->addStmtp(top_in_var);
        m_modp->addStmtp(top_out_var);
        auto invar_in_newdut = invar->cloneTree(false);
        auto outvar_in_newdut = outvar->cloneTree(false);
        m_new_dut_modp->addStmtp(invar_in_newdut);
        m_new_dut_modp->addStmtp(outvar_in_newdut);
        clktree_module->addStmtp(invar);
        clktree_module->addStmtp(outvar);
        clktree_module->addStmtp(assign);
        append_pin_in_list(pin_in_clocktree,
                           new AstPin(nullptr, 0, in_var_name, top_in_var_in_cell));
        append_pin_in_list(pin_in_clocktree,
                           new AstPin(nullptr, 0, out_var_name, top_out_var_in_cell));
        append_pin_in_list(pin_in_newdut, new AstPin(nullptr, 0, out_var_name,
                                                     top_in_var_in_cell->cloneTree(false)));
        append_pin_in_list(pin_in_newdut, new AstPin(nullptr, 0, in_var_name,
                                                     top_out_var_in_cell->cloneTree(false)));
        RemoveVarVisitor remove_visitor{m_new_dut_modp, var->name(),
                                        invar_in_newdut, outvar_in_newdut};
    }
    auto cell_clocktree = new AstCell(nullptr, nullptr, "_0_", "Vtop_ClockTree", pin_in_clocktree,
                               nullptr, nullptr);
    auto cell_new_dut = new AstCell(nullptr, nullptr, "_1_", "Vtop___024root", pin_in_newdut,
                                      nullptr, nullptr);
    m_modp->addStmtp(cell_clocktree);
    m_modp->addStmtp(cell_new_dut);

    partition::verilogForTree(clktree_module, clockTree);
    VL_DO_DANGLING(pushDeletep(clktree_module), clktree_module);
}

void ClockExtractVisitor::build() 
{
    build_clocktree();
    Clock::DivideGraph v(m_new_dut_modp);
    v.process();
}

void V3ClockExtrect::extractAll(AstNetlist* nodep)
{
    ClockExtractVisitor visitor(nodep);
    visitor.build();
    #if 0
    printf("begin print m_modp\n");
    partition::verilogForTree(visitor.m_modp);
    printf("end print m_modp\n");
    printf("begin print m_new_dut_modp\n");
    partition::verilogForTree(visitor.m_new_dut_modp);
    printf("end print m_new_dut_modp\n");
    #endif
}