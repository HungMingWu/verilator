#include <fstream>
#include <string>
#include "V3Ast.h"
#include "V3ClockExtract.h"
#include "V3EmitCBase.h"
#include "V3OrderGraph.h"
#include "V3AstUserAllocator.h"

struct CollectPort final : public EmitCBaseVisitor {
    std::vector<AstVar*> m_vars;

    void visit(AstVar* nodep) override {
        if (nodep->isIO()) m_vars.push_back(nodep);
    }
    void visit(AstNode* nodep) override { iterateChildrenConst(nodep); };

    CollectPort(AstNodeModule* nodep) { iterate(nodep); }
    ~CollectPort() = default;
};

namespace Clock {

class EmitVBaseVisitor VL_NOT_FINAL : public EmitCBaseVisitor {
    // MEMBERS
    bool m_suppressSemi = false;
    const bool m_suppressUnknown = false;
    AstSenTree* m_sensesp;  // Domain for printing one a ALWAYS under a ACTIVE

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    virtual void puts(const string& str) = 0;
    virtual void putbs(const string& str) = 0;
    virtual void putfs(AstNode* nodep, const string& str) = 0;  // Fileline and node %% mark
    virtual void putqs(AstNode* nodep, const string& str) = 0;  // Fileline quiet w/o %% mark
    virtual void putsNoTracking(const string& str) = 0;
    virtual void putsQuoted(const string& str) {
        // Quote \ and " for use inside C programs
        // Don't use to quote a filename for #include - #include doesn't \ escape.
        // Duplicate in V3File - here so we can print to string
        putsNoTracking("\"");
        putsNoTracking(V3OutFormatter::quoteNameControls(str));
        putsNoTracking("\"");
    }

    // VISITORS
    virtual void visit(AstNetlist* nodep) override { iterateAndNextConstNull(nodep->modulesp()); }
    virtual void visit(AstNodeModule* nodep) override {
        CollectPort visitor(nodep);
        putfs(nodep, nodep->verilogKwd() + " " + prefixNameProtect(nodep) + "(");
        for (size_t i = 0; i < visitor.m_vars.size(); i++) {
            if (i) putfs(nodep, ", ");
            putfs(nodep, visitor.m_vars[i]->name());
        }
        putfs(nodep, ");\n");
        iterateChildrenConst(nodep);
        putqs(nodep, "end" + nodep->verilogKwd() + "\n");
    }
    virtual void visit(AstPort* nodep) override {}
    virtual void visit(AstNodeFTask* nodep) override {
        putfs(nodep, nodep->isFunction() ? "function" : "task");
        puts(" ");
        puts(nodep->name());
        puts(";\n");
        // Only putfs the first time for each visitor; later for same node is putqs
        iterateAndNextConstNull(nodep->stmtsp());
        putfs(nodep, nodep->isFunction() ? "endfunction\n" : "endtask\n");
    }

    virtual void visit(AstBegin* nodep) override {
        if (nodep->name() == "") {
            putbs("begin\n");
        } else {
            putbs("begin : " + nodep->name() + "\n");
        }
        iterateChildrenConst(nodep);
        puts("end\n");
    }
    virtual void visit(AstFork* nodep) override {
        if (nodep->name() == "") {
            putbs("fork\n");
        } else {
            putbs("fork : " + nodep->name() + "\n");
        }
        iterateChildrenConst(nodep);
        puts(nodep->joinType().verilogKwd());
        puts("\n");
    }
    virtual void visit(AstFinal* nodep) override {
        putfs(nodep, "final begin\n");
        iterateChildrenConst(nodep);
        putqs(nodep, "end\n");
    }
    virtual void visit(AstInitial* nodep) override {
        putfs(nodep, "initial begin\n");
        iterateChildrenConst(nodep);
        putqs(nodep, "end\n");
    }
    virtual void visit(AstInitialAutomatic* nodep) override { iterateChildrenConst(nodep); }
    virtual void visit(AstInitialStatic* nodep) override { iterateChildrenConst(nodep); }
    virtual void visit(AstAlways* nodep) override {
        putfs(nodep, "always ");
        if (m_sensesp) {
            iterateAndNextConstNull(m_sensesp);
        }  // In active
        else {
            iterateAndNextConstNull(nodep->sensesp());
        }
        putbs(" begin\n");
        iterateAndNextConstNull(nodep->bodysp());
        putqs(nodep, "end\n");
    }
    virtual void visit(AstAlwaysPublic* nodep) override {
        putfs(nodep, "/*verilator public_flat_rw ");
        if (m_sensesp) {
            iterateAndNextConstNull(m_sensesp);
        }  // In active
        else {
            iterateAndNextConstNull(nodep->sensesp());
        }
        putqs(nodep, " ");
        iterateAndNextConstNull(nodep->bodysp());
        putqs(nodep, "*/\n");
    }
    virtual void visit(AstNodeAssign* nodep) override {
        if (VN_IS(nodep, AssignForce)) puts("force ");
        iterateAndNextConstNull(nodep->lhsp());
        putfs(nodep, " " + nodep->verilogKwd() + " ");
        iterateAndNextConstNull(nodep->rhsp());
        if (!m_suppressSemi) puts(";\n");
    }
    virtual void visit(AstAssignDly* nodep) override {
        iterateAndNextConstNull(nodep->lhsp());
        putfs(nodep, " <= ");
        iterateAndNextConstNull(nodep->rhsp());
        puts(";\n");
    }
    virtual void visit(AstAssignAlias* nodep) override {
        putbs("alias ");
        iterateAndNextConstNull(nodep->lhsp());
        putfs(nodep, " = ");
        iterateAndNextConstNull(nodep->rhsp());
        if (!m_suppressSemi) puts(";\n");
    }
    virtual void visit(AstAssignW* nodep) override {
        putfs(nodep, "assign ");
        iterateAndNextConstNull(nodep->lhsp());
        putbs(" = ");
        iterateAndNextConstNull(nodep->rhsp());
        if (!m_suppressSemi) puts(";\n");
    }
    virtual void visit(AstRelease* nodep) override {
        puts("release ");
        iterateAndNextConstNull(nodep->lhsp());
        if (!m_suppressSemi) puts(";\n");
    }
    virtual void visit(AstBreak*) override {
        putbs("break");
        if (!m_suppressSemi) puts(";\n");
    }
    virtual void visit(AstSenTree* nodep) override {
        // AstSenItem is called for dumping in isolation by V3Order
        putfs(nodep, "@(");
        for (AstNode* expp = nodep->sensesp(); expp; expp = expp->nextp()) {
            iterate(expp);
            if (expp->nextp()) putqs(expp->nextp(), " or ");
        }
        puts(")");
    }
    virtual void visit(AstSenItem* nodep) override {
        putfs(nodep, "");
        puts(nodep->edgeType().verilogKwd());
        if (nodep->sensp()) puts(" ");
        iterateChildrenConst(nodep);
    }
    virtual void visit(AstNodeCase* nodep) override {
        putfs(nodep, "");
        if (const AstCase* const casep = VN_CAST(nodep, Case)) {
            if (casep->priorityPragma()) puts("priority ");
            if (casep->uniquePragma()) puts("unique ");
            if (casep->unique0Pragma()) puts("unique0 ");
        }
        puts(nodep->verilogKwd());
        puts(" (");
        iterateAndNextConstNull(nodep->exprp());
        puts(")\n");
        if (const AstCase* const casep = VN_CAST(nodep, Case)) {
            if (casep->fullPragma() || casep->parallelPragma()) {
                puts(" // synopsys");
                if (casep->fullPragma()) puts(" full_case");
                if (casep->parallelPragma()) puts(" parallel_case");
            }
        }
        iterateAndNextConstNull(nodep->itemsp());
        putqs(nodep, "endcase\n");
    }
    virtual void visit(AstCaseItem* nodep) override {
        if (nodep->condsp()) {
            iterateAndNextConstNull(nodep->condsp());
        } else {
            putbs("default");
        }
        putfs(nodep, ": begin ");
        iterateAndNextConstNull(nodep->bodysp());
        putqs(nodep, "end\n");
    }
    virtual void visit(AstComment* nodep) override {
        puts(string("// ") + nodep->name() + "\n");
        iterateChildrenConst(nodep);
    }
    virtual void visit(AstContinue*) override {
        putbs("continue");
        if (!m_suppressSemi) puts(";\n");
    }
    virtual void visit(AstCoverDecl*) override {}  // N/A
    virtual void visit(AstCoverInc*) override {}  // N/A
    virtual void visit(AstCoverToggle*) override {}  // N/A

    void visitNodeDisplay(AstNode* nodep, AstNode* fileOrStrgp, const string& text,
                          AstNode* exprsp) {
        putfs(nodep, nodep->verilogKwd());
        putbs("(");
        if (fileOrStrgp) {
            iterateAndNextConstNull(fileOrStrgp);
            putbs(", ");
        }
        putsQuoted(text);
        for (AstNode* expp = exprsp; expp; expp = expp->nextp()) {
            puts(", ");
            iterateAndNextConstNull(expp);
        }
        puts(");\n");
    }
    virtual void visit(AstDisable* nodep) override { putbs("disable " + nodep->name() + ";\n"); }
    virtual void visit(AstDisplay* nodep) override {
        visitNodeDisplay(nodep, nodep->filep(), nodep->fmtp()->text(), nodep->fmtp()->exprsp());
    }
    virtual void visit(AstElabDisplay* nodep) override {
        visitNodeDisplay(nodep, nullptr, nodep->fmtp()->text(), nodep->fmtp()->exprsp());
    }
    virtual void visit(AstFScanF* nodep) override {
        visitNodeDisplay(nodep, nodep->filep(), nodep->text(), nodep->exprsp());
    }
    virtual void visit(AstSScanF* nodep) override {
        visitNodeDisplay(nodep, nodep->fromp(), nodep->text(), nodep->exprsp());
    }
    virtual void visit(AstSFormat* nodep) override {
        visitNodeDisplay(nodep, nodep->lhsp(), nodep->fmtp()->text(), nodep->fmtp()->exprsp());
    }
    virtual void visit(AstSFormatF* nodep) override {
        visitNodeDisplay(nodep, nullptr, nodep->text(), nodep->exprsp());
    }
    virtual void visit(AstFOpen* nodep) override {
        putfs(nodep, nodep->verilogKwd());
        putbs("(");
        iterateAndNextConstNull(nodep->filenamep());
        putbs(", ");
        iterateAndNextConstNull(nodep->modep());
        puts(");\n");
    }
    virtual void visit(AstFOpenMcd* nodep) override {
        putfs(nodep, nodep->verilogKwd());
        putbs("(");
        iterateAndNextConstNull(nodep->filenamep());
        puts(");\n");
    }
    virtual void visit(AstFClose* nodep) override {
        putfs(nodep, nodep->verilogKwd());
        putbs("(");
        if (nodep->filep()) iterateAndNextConstNull(nodep->filep());
        puts(");\n");
    }
    virtual void visit(AstFFlush* nodep) override {
        putfs(nodep, nodep->verilogKwd());
        putbs("(");
        if (nodep->filep()) iterateAndNextConstNull(nodep->filep());
        puts(");\n");
    }
    virtual void visit(AstJumpBlock* nodep) override {
        putbs("begin : label" + cvtToStr(nodep->labelNum()) + "\n");
        if (nodep->stmtsp()) iterateAndNextConstNull(nodep->stmtsp());
        puts("end\n");
    }
    virtual void visit(AstJumpGo* nodep) override {
        putbs("disable label" + cvtToStr(nodep->labelp()->blockp()->labelNum()) + ";\n");
    }
    virtual void visit(AstJumpLabel* nodep) override {
        putbs("// " + cvtToStr(nodep->blockp()) + ":\n");
    }
    virtual void visit(AstNodeReadWriteMem* nodep) override {
        putfs(nodep, nodep->verilogKwd());
        putbs("(");
        if (nodep->filenamep()) iterateAndNextConstNull(nodep->filenamep());
        putbs(", ");
        if (nodep->memp()) iterateAndNextConstNull(nodep->memp());
        if (nodep->lsbp()) {
            putbs(", ");
            iterateAndNextConstNull(nodep->lsbp());
        }
        if (nodep->msbp()) {
            putbs(", ");
            iterateAndNextConstNull(nodep->msbp());
        }
        puts(");\n");
    }
    virtual void visit(AstSysFuncAsTask* nodep) override {
        iterateAndNextConstNull(nodep->lhsp());
        puts(";\n");
    }
    virtual void visit(AstSysIgnore* nodep) override {
        putfs(nodep, nodep->verilogKwd());
        putbs("(");
        iterateAndNextConstNull(nodep->exprsp());
        puts(");\n");
    }
    virtual void visit(AstNodeFor* nodep) override {
        putfs(nodep, "for (");
        {
            VL_RESTORER(m_suppressSemi);
            m_suppressSemi = true;
            iterateAndNextConstNull(nodep->initsp());
            puts(";");
            iterateAndNextConstNull(nodep->condp());
            puts(";");
            iterateAndNextConstNull(nodep->incsp());
        }
        puts(") begin\n");
        iterateAndNextConstNull(nodep->bodysp());
        putqs(nodep, "end\n");
    }
    virtual void visit(AstRepeat* nodep) override {
        putfs(nodep, "repeat (");
        iterateAndNextConstNull(nodep->countp());
        puts(") begin\n");
        iterateAndNextConstNull(nodep->bodysp());
        putfs(nodep, "end\n");
    }
    virtual void visit(AstWhile* nodep) override {
        iterateAndNextConstNull(nodep->precondsp());
        putfs(nodep, "while (");
        iterateAndNextConstNull(nodep->condp());
        puts(") begin\n");
        iterateAndNextConstNull(nodep->bodysp());
        iterateAndNextConstNull(nodep->incsp());
        iterateAndNextConstNull(nodep->precondsp());  // Need to recompute before next loop
        putfs(nodep, "end\n");
    }
    virtual void visit(AstNodeIf* nodep) override {
        putfs(nodep, "");
        if (const AstIf* const ifp = VN_CAST(nodep, If)) {
            if (ifp->priorityPragma()) puts("priority ");
            if (ifp->uniquePragma()) puts("unique ");
            if (ifp->unique0Pragma()) puts("unique0 ");
        }
        puts("if (");
        iterateAndNextConstNull(nodep->condp());
        puts(") begin\n");
        iterateAndNextConstNull(nodep->ifsp());
        if (nodep->elsesp()) {
            putqs(nodep, "end\n");
            putqs(nodep, "else begin\n");
            iterateAndNextConstNull(nodep->elsesp());
        }
        putqs(nodep, "end\n");
    }
    virtual void visit(AstPast* nodep) override {
        putfs(nodep, "$past(");
        iterateAndNextConstNull(nodep->exprp());
        if (nodep->ticksp()) {
            puts(", ");
            iterateAndNextConstNull(nodep->ticksp());
        }
        puts(")");
    }
    virtual void visit(AstReturn* nodep) override {
        putfs(nodep, "return ");
        iterateAndNextConstNull(nodep->lhsp());
        puts(";\n");
    }
    virtual void visit(AstStop* nodep) override { putfs(nodep, "$stop;\n"); }
    virtual void visit(AstFinish* nodep) override { putfs(nodep, "$finish;\n"); }
    virtual void visit(AstNodeSimpleText* nodep) override {
        if (nodep->tracking() || m_trackText) {
            puts(nodep->text());
        } else {
            putsNoTracking(nodep->text());
        }
    }
    virtual void visit(AstTextBlock* nodep) override {
        visit(static_cast<AstNodeSimpleText*>(nodep));
        {
            VL_RESTORER(m_suppressSemi);
            m_suppressVarSemi = nodep->commas();
            for (AstNode* childp = nodep->nodesp(); childp; childp = childp->nextp()) {
                iterate(childp);
                if (nodep->commas() && childp->nextp()) puts(", ");
            }
        }
    }
    virtual void visit(AstScopeName* nodep) override {}
    virtual void visit(AstCStmt* nodep) override {
        putfs(nodep, "$_CSTMT(");
        iterateAndNextConstNull(nodep->bodysp());
        puts(");\n");
    }
    virtual void visit(AstCMath* nodep) override {
        putfs(nodep, "$_CMATH(");
        iterateAndNextConstNull(nodep->bodysp());
        puts(");\n");
    }
    virtual void visit(AstUCStmt* nodep) override {
        putfs(nodep, "$c(");
        iterateAndNextConstNull(nodep->bodysp());
        puts(");\n");
    }
    virtual void visit(AstUCFunc* nodep) override {
        putfs(nodep, "$c(");
        iterateAndNextConstNull(nodep->bodysp());
        puts(")");
    }

    // Operators
    virtual void emitVerilogFormat(AstNode* nodep, const string& format, AstNode* lhsp = nullptr,
                                   AstNode* const rhsp = nullptr, AstNode* thsp = nullptr,
                                   AstNode* fhsp = nullptr) {
        // Look at emitVerilog() format for term/uni/dual/triops,
        // and write out appropriate text.
        //      %f      Potential fileline-if-change and line break
        //      %l      lhsp - if appropriate
        //      %r      rhsp - if appropriate
        //      %t      thsp - if appropriate
        //      %o      fhsp - if appropriate
        //      %d      dtypep - if appropriate
        //      %k      Potential line break
        bool inPct = false;
        putbs("");
        for (const char c : format) {
            if (c == '%') {
                inPct = true;
            } else if (!inPct) {  // Normal text
                string s;
                s += c;
                puts(s);
            } else {  // Format character
                inPct = false;
                switch (c) {
                case '%': puts("%"); break;
                case 'f': putfs(nodep, ""); break;
                case 'k': putbs(""); break;
                case 'l': {
                    UASSERT_OBJ(lhsp, nodep, "emitVerilog() references undef node");
                    iterateAndNextConstNull(lhsp);
                    break;
                }
                case 'r': {
                    UASSERT_OBJ(rhsp, nodep, "emitVerilog() references undef node");
                    iterateAndNextConstNull(rhsp);
                    break;
                }
                case 't': {
                    UASSERT_OBJ(thsp, nodep, "emitVerilog() references undef node");
                    iterateAndNextConstNull(thsp);
                    break;
                }
                case 'o': {
                    UASSERT_OBJ(thsp, nodep, "emitVerilog() references undef node");
                    iterateAndNextConstNull(fhsp);
                    break;
                }
                case 'd': {
                    UASSERT_OBJ(nodep->dtypep(), nodep, "emitVerilog() references undef node");
                    iterateAndNextConstNull(nodep->dtypep());
                    break;
                }
                default: nodep->v3fatalSrc("Unknown emitVerilog format code: %" << c); break;
                }
            }
        }
    }

    virtual void visit(AstNodeTermop* nodep) override {
        emitVerilogFormat(nodep, nodep->emitVerilog());
    }
    virtual void visit(AstNodeUniop* nodep) override {
        emitVerilogFormat(nodep, nodep->emitVerilog(), nodep->lhsp());
    }
    virtual void visit(AstNodeBiop* nodep) override {
        emitVerilogFormat(nodep, nodep->emitVerilog(), nodep->lhsp(), nodep->rhsp());
    }
    virtual void visit(AstNodeTriop* nodep) override {
        emitVerilogFormat(nodep, nodep->emitVerilog(), nodep->lhsp(), nodep->rhsp(),
                          nodep->thsp());
    }
    virtual void visit(AstAttrOf* nodep) override {
        putfs(nodep, "$_ATTROF(");
        iterateAndNextConstNull(nodep->fromp());
        if (nodep->dimp()) {
            putbs(", ");
            iterateAndNextConstNull(nodep->dimp());
        }
        puts(")");
    }
    virtual void visit(AstInitArray* nodep) override {
        putfs(nodep, "'{");
        int comma = 0;
        const auto& mapr = nodep->map();
        for (const auto& itr : mapr) {
            if (comma++) putbs(", ");
            puts(cvtToStr(itr.first));
            puts(":");
            AstNode* const valuep = itr.second->valuep();
            iterate(valuep);
        }
        puts("}");
    }
    virtual void visit(AstNodeCond* nodep) override {
        putbs("(");
        iterateAndNextConstNull(nodep->condp());
        putfs(nodep, " ? ");
        iterateAndNextConstNull(nodep->expr1p());
        putbs(" : ");
        iterateAndNextConstNull(nodep->expr2p());
        puts(")");
    }
    virtual void visit(AstRange* nodep) override {
        puts("[");
        if (VN_IS(nodep->leftp(), Const) && VN_IS(nodep->rightp(), Const)) {
            // Looks nicer if we print [1:0] rather than [32'sh1:32sh0]
            puts(cvtToStr(nodep->leftConst()));
            puts(":");
            puts(cvtToStr(nodep->rightConst()));
            puts("]");
        } else {
            iterateAndNextConstNull(nodep->leftp());
            puts(":");
            iterateAndNextConstNull(nodep->rightp());
            puts("]");
        }
    }
    virtual void visit(AstSel* nodep) override {
        iterateAndNextConstNull(nodep->fromp());
        puts("[");
        if (VN_IS(nodep->lsbp(), Const)) {
            if (nodep->widthp()->isOne()) {
                if (VN_IS(nodep->lsbp(), Const)) {
                    puts(cvtToStr(VN_AS(nodep->lsbp(), Const)->toSInt()));
                } else {
                    iterateAndNextConstNull(nodep->lsbp());
                }
            } else {
                puts(cvtToStr(VN_AS(nodep->lsbp(), Const)->toSInt()
                              + VN_AS(nodep->widthp(), Const)->toSInt() - 1));
                puts(":");
                puts(cvtToStr(VN_AS(nodep->lsbp(), Const)->toSInt()));
            }
        } else {
            iterateAndNextConstNull(nodep->lsbp());
            putfs(nodep, "+:");
            iterateAndNextConstNull(nodep->widthp());
            puts("]");
        }
        puts("]");
    }
    virtual void visit(AstSliceSel* nodep) override {
        iterateAndNextConstNull(nodep->fromp());
        puts(cvtToStr(nodep->declRange()));
    }
    virtual void visit(AstTypedef* nodep) override {
        putfs(nodep, "typedef ");
        iterateAndNextConstNull(nodep->dtypep());
        puts(" ");
        puts(nodep->name());
        puts(";\n");
    }
    virtual void visit(AstBasicDType* nodep) override {
        if (nodep->isSigned()) putfs(nodep, "signed ");
        putfs(nodep, nodep->name());
        if (nodep->rangep()) {
            puts(" ");
            iterateAndNextConstNull(nodep->rangep());
            puts(" ");
        } else if (nodep->isRanged()) {
            puts(" [");
            puts(cvtToStr(nodep->hi()));
            puts(":0] ");
        }
    }
    virtual void visit(AstConstDType* nodep) override {
        putfs(nodep, "const ");
        iterate(nodep->subDTypep());
    }
    virtual void visit(AstNodeArrayDType* nodep) override {
        iterate(nodep->subDTypep());
        iterateAndNextConstNull(nodep->rangep());
    }
    virtual void visit(AstNodeUOrStructDType* nodep) override {
        puts(nodep->verilogKwd() + " ");
        if (nodep->packed()) puts("packed ");
        puts("\n");
        puts("{");
        iterateAndNextConstNull(nodep->membersp());
        puts("}");
    }
    virtual void visit(AstMemberDType* nodep) override {
        iterate(nodep->subDTypep());
        puts(" ");
        puts(nodep->name());
    }
    virtual void visit(AstNodeFTaskRef* nodep) override {
        if (nodep->dotted() != "") {
            putfs(nodep, nodep->dotted());
            puts(".");
            puts(nodep->name());
        } else {
            putfs(nodep, nodep->name());
        }
        puts("(");
        iterateAndNextConstNull(nodep->pinsp());
        puts(")");
    }
    virtual void visit(AstArg* nodep) override { iterateAndNextConstNull(nodep->exprp()); }
    virtual void visit(AstPrintTimeScale* nodep) override {
        puts(nodep->verilogKwd());
        puts(";\n");
    }
    virtual void visit(AstCell* nodep) override {
        putfs(nodep, nodep->modName() + " " + nodep->name() + "(\n");
        AstPin* list = nodep->pinsp();
        bool first = true;
        while (list) {
            if (!first) putfs(nodep, ", ");
            first = false;
            putfs(nodep, "." + list->name() + "(" + list->exprp()->name() + ")");
            list = static_cast<AstPin*>(list->nextp());
        }
        putfs(nodep, ");\n");
    }

    // Terminals
    virtual void visit(AstVarRef* nodep) override {
        if (nodep->varScopep()) {
#if 0
            putfs(nodep, nodep->varScopep()->name());
#else
            putfs(nodep, nodep->varp()->name());
#endif
        } else {
            if (nodep->varp()) {
#if 1
                if (nodep->selfPointer().empty()) {
                    putfs(nodep, nodep->varp()->name());
                } else {
                    putfs(nodep, nodep->selfPointer() + "->");
                    puts(nodep->varp()->name());
                }
#else
                putfs(nodep, nodep->varp()->name());
#endif
            } else {
                putfs(nodep, nodep->name());
            }
        }
    }
    virtual void visit(AstVarXRef* nodep) override {
        putfs(nodep, nodep->dotted());
        puts(".");
        if (nodep->varp()) {
            puts(nodep->varp()->name());
        } else {
            puts(nodep->name());
        }
    }
    virtual void visit(AstConst* nodep) override { putfs(nodep, nodep->num().ascii(true, true)); }

    // Just iterate
    virtual void visit(AstTopScope* nodep) override { iterateChildrenConst(nodep); }
    virtual void visit(AstScope* nodep) override { iterateChildrenConst(nodep); }
    virtual void visit(AstVar* nodep) override {
        if (nodep->isIO()) {
            putfs(nodep, nodep->verilogKwd());
            puts(" ");
        }
        std::vector<const AstUnpackArrayDType*> unpackps;
        for (AstNodeDType* dtypep = nodep->dtypep(); dtypep;) {
            dtypep = dtypep->skipRefp();
            if (const AstUnpackArrayDType* const unpackp = VN_CAST(dtypep, UnpackArrayDType)) {
                unpackps.push_back(unpackp);
                dtypep = unpackp->subDTypep();
            } else {
                iterate(dtypep);
                puts(" ");
                puts(nodep->name());
                dtypep = nullptr;
            }
        }
        // If nodep is an unpacked array, append unpacked dimensions
        for (const auto& unpackp : unpackps) {
            puts("[");
            puts(cvtToStr(unpackp->rangep()->leftConst()));
            puts(":");
            puts(cvtToStr(unpackp->rangep()->rightConst()));
            puts("]");
        }
        puts(m_suppressVarSemi ? "\n" : ";\n");
    }
    virtual void visit(AstActive* nodep) override {
        m_sensesp = nodep->sensesp();
        iterateAndNextConstNull(nodep->stmtsp());
        m_sensesp = nullptr;
    }
    virtual void visit(AstParseRef* nodep) override { puts(nodep->name()); }
    virtual void visit(AstVarScope*) override {}
    virtual void visit(AstNodeText*) override {}
    virtual void visit(AstTraceDecl*) override {}
    virtual void visit(AstTraceInc*) override {}
    // NOPs
    virtual void visit(AstPragma*) override {}
    // Default
    virtual void visit(AstNode* nodep) override {
        puts(string("\n???? // ") + nodep->prettyTypeName() + "\n");
        iterateChildrenConst(nodep);
        // Not v3fatalSrc so we keep processing
        if (!m_suppressUnknown) {
            nodep->v3error(
                "Internal: Unknown node type reached emitter: " << nodep->prettyTypeName());
        }
    }

public:
    bool m_suppressVarSemi = false;  // Suppress emitting semicolon for AstVars
    explicit EmitVBaseVisitor(bool suppressUnknown, AstSenTree* domainp)
        : m_suppressUnknown{suppressUnknown}
        , m_sensesp{domainp} {}
    virtual ~EmitVBaseVisitor() override = default;
};

class EmitVStreamVisitor final : public EmitVBaseVisitor {
    // MEMBERS
    std::ostream& m_os;
    // METHODS
    virtual void putsNoTracking(const string& str) override { m_os << str; }
    virtual void puts(const string& str) override { putsNoTracking(str); }
    virtual void putbs(const string& str) override { puts(str); }
    virtual void putfs(AstNode*, const string& str) override { putbs(str); }
    virtual void putqs(AstNode*, const string& str) override { putbs(str); }

public:
    EmitVStreamVisitor(const AstNode* nodep, std::ostream& os)
        : EmitVBaseVisitor{false, nullptr}
        , m_os(os) {  // Need () or GCC 4.8 false warning
        iterate(const_cast<AstNode*>(nodep));
    }
    virtual ~EmitVStreamVisitor() override = default;
};

}  // namespace Clock

class RemoveVarVisitor final : public VNVisitor 
{
    std::string m_target_name;
    AstVar* m_newtarget;
    virtual void visit(AstVarRef* nodep) 
    { 
        if (nodep->varp() && nodep->varp()->name() == m_target_name)
        { 
            printf("found target, change it\n");
            nodep->varp(m_newtarget);
        }
    }
    // Default
    virtual void visit(AstNode* nodep) override 
    { 
        iterateChildrenConst(nodep);
    }

public:
    RemoveVarVisitor(AstNodeModule *nodep, std::string target_name, AstVar* newtarget)
        : m_target_name(target_name)
        , m_newtarget(newtarget)
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
            CollectPort c(m_new_dut_modp);
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
    CollectPort c(m_new_dut_modp);
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
        auto outvar_in_newdut = outvar->cloneTree(false);
        m_new_dut_modp->addStmtp(invar->cloneTree(false));
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
        RemoveVarVisitor remove_visitor{m_new_dut_modp, var->name(), outvar_in_newdut};
    }
    auto cell_clocktree = new AstCell(nullptr, nullptr, "_0_", "Vtop_ClockTree", pin_in_clocktree,
                               nullptr, nullptr);
    auto cell_new_dut = new AstCell(nullptr, nullptr, "_1_", "Vtop___024root", pin_in_newdut,
                                      nullptr, nullptr);
    m_modp->addStmtp(cell_clocktree);
    m_modp->addStmtp(cell_new_dut);

    Clock::EmitVStreamVisitor v{clktree_module, clockTree};
    VL_DO_DANGLING(pushDeletep(clktree_module), clktree_module);
}

void ClockExtractVisitor::build() 
{
    build_clocktree();
}

void V3ClockExtrect::extractAll(AstNetlist* nodep)
{
    ClockExtractVisitor visitor(nodep);
    visitor.build();
    printf("begin print m_modp\n");
    Clock::EmitVStreamVisitor v1{visitor.m_modp, std::cout};
    printf("end print m_modp\n");
    printf("begin print m_new_dut_modp\n");
    Clock::EmitVStreamVisitor v2{visitor.m_new_dut_modp, std::cout};
    printf("end print m_new_dut_modp\n");
}