#include <fstream>
#include <string>
#include "V3Ast.h"
#include "V3DividePartition.h"
#include "V3EmitCBase.h"
#include "V3OrderGraph.h"
#include "V3AstUserAllocator.h"
#include "partition/V3EmitV.h"
#include "partition/V3Utils.h"

inline void append_pin_in_list(AstPin*& last, AstPin* newpin) {
    if (last == nullptr)
        last = newpin;
    else
        last = static_cast<AstPin*>(last->addNext(newpin));
}

class DividePartitionVisitor final : public VNVisitor {
    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    static const size_t num_partitions = 4;

    struct State {
        size_t index{};
        size_t scores{};
        std::set<AstVar*> m_vars;
        std::set<AstVarScope*> m_varScopes;
    };

    std::unordered_map<AstActive*, State> m_states;

    // STATE
    AstNodeModule* m_new_dut_modp = nullptr;
    AstActive* m_curActive = nullptr;
    std::size_t curIdx = 0;

    // VISITORS
    virtual void visit(AstAssignDly* nodep) override {
        if (!m_curActive) {
            printf("ddddddddddddddddddddddd\n");
            return;  // No process module exist, ignore it
        }
        m_states[m_curActive].scores++;
        iterateChildren(nodep);
    }
    virtual void visit(AstNodeVarRef* nodep) override {
        if (!m_curActive) return;  // No process module exist, ignore it
        if (AstVarScope* varscopep = nodep->varScopep()) {
            m_states[m_curActive].m_varScopes.insert(varscopep);
            if (varscopep->varp()) m_states[m_curActive].m_vars.insert(varscopep->varp());
        }
        iterateChildren(nodep);
    }

    virtual void visit(AstActive* nodep) override {
        if (nodep->sensesp()->hasCombo()) return;
        VL_RESTORER(m_curActive);
        m_curActive = nodep;
        printf("Assign active %p to idx %d\n", nodep, curIdx);
        m_states[m_curActive].index = curIdx;
        curIdx = (curIdx + 1) % num_partitions;
        iterateChildren(nodep);
        if (m_states[m_curActive].scores == 0) { m_states.erase(m_curActive); }
    }


    virtual void visit(AstNodeModule* nodep) override {
        if (!m_new_dut_modp) {
            m_new_dut_modp = nodep->cloneTree(true);
            // preprocess
            partition::cleanAll(m_new_dut_modp);
            partition::expandAll(m_new_dut_modp);
            #if 0
            partition::mergeAll(m_new_dut_modp);
            #endif
            iterateChildren(m_new_dut_modp);
            pushDeletep(m_new_dut_modp);
            for (size_t i = 0; i < num_partitions; i++)
            {
                AstPin* pin_in_cell = nullptr;
                std::string part_cell_name = "part_" + std::to_string(i + 1);
                auto m_curProcessMod = new AstModule(nullptr, part_cell_name, false);
                std::set<AstVar*> vars;
                std::set<AstVarScope*> varscopes;
                std::vector<AstActive*> actives;
                for (auto& pair : m_states) {
                    if (pair.second.index != i) continue;
                    std::copy(pair.second.m_vars.begin(), pair.second.m_vars.end(),
                              inserter(vars, vars.begin()));
                    std::copy(pair.second.m_varScopes.begin(), pair.second.m_varScopes.end(),
                              inserter(varscopes, varscopes.begin()));
                    actives.push_back(pair.first);
                }
                // Insert var in active into new cell
                for (auto& var : vars) {
                    auto newvar = var->cloneTree(false);
                    if (!var->isIO())
                        var->direction(VDirection::OUTPUT);  // Mark the var to output port
                    auto newvarRef = new AstVarRef(nullptr, newvar, VAccess::READ);
                    var->replaceWith(newvar);
                    append_pin_in_list(pin_in_cell,
                        new AstPin(nullptr, 0, var->name(), newvarRef));
                    m_curProcessMod->addStmtp(var);
                }
                AstScope* scopep = new AstScope(nullptr, m_curProcessMod, "top", nullptr, nullptr);
                m_curProcessMod->addStmtp(scopep);
                for (auto& varscopep : varscopes) {
                    varscopep->unlinkFrBack();
                    varscopep->scopep(scopep);
                    m_curProcessMod->addStmtp(varscopep);
                }
                for (auto& active : actives) {
                    active->unlinkFrBack();
                    m_curProcessMod->addStmtp(active);
                }
                auto cell_partp = new AstCell(nullptr, nullptr, "_" + std::to_string(i + 1) + "_",
                                              part_cell_name, pin_in_cell, nullptr, nullptr);
                m_new_dut_modp->addStmtp(cell_partp);
                std::ofstream ofs(part_cell_name + ".sv", std::ofstream::out);
                partition::verilogForTree(m_curProcessMod, part_cell_name, ofs);
                pushDeletep(m_curProcessMod);
            }
            std::ofstream ofs("new_top.sv", std::ofstream::out);
            partition::verilogForTree(m_new_dut_modp, "top", ofs);
        }
    }

    virtual void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit DividePartitionVisitor(AstNetlist* nodep) { iterate(nodep); }
    virtual ~DividePartitionVisitor() override = default;
};

void V3DividePartition::extractAll(AstNetlist* nodep) {
    DividePartitionVisitor visitor(nodep);
#if 0
    printf("begin print m_new_dut_modp\n");
    partition::verilogForTree(visitor.m_new_dut_modp);
    printf("end print m_new_dut_modp\n");
#endif
}
