#include <queue>
#include "V3EmitCBase.h"
#include "V3Stats.h"
#include "V3Utils.h"
#include "V3AstUserAllocator.h"
#include "V3Hasher.h"
#include "V3DupFinder.h"
#include "../V3EmitV.h"

class CleanUnusedVarVisitor VL_NOT_FINAL : public EmitCBaseVisitor {
	std::set<AstVar*> m_vars;
	virtual void visit(AstVarRef* nodep) override {
		AstVarScope* varscopep = nodep->varScopep();
		AstVar* varp = nullptr;
		if (varscopep) varp = varscopep->varp();
		printf("Found a new astvarref %p, name is %s\n", varp, varp->name().c_str());
		if (m_vars.count(varp)) {
			m_vars.erase(varp);
		}
		iterateChildrenConst(nodep);
	}
	virtual void visit(AstVar* nodep) override {
		printf("Found a new astvar %p, name is %s\n", nodep, nodep->name().c_str());
		m_vars.insert(nodep);
	}
	virtual void visit(AstNode* nodep) override { iterateChildrenConst(nodep); }
public:
	CleanUnusedVarVisitor(AstNodeModule* nodep)
	{
#if 0
		printf("Begin Clean unusedVar\n");
		nodep->dumpTree("", 30);
		printf("End Clean unusedVar\n");
#endif
		iterate(nodep);
#if 0
		for (auto& varp : m_vars)
		{
			printf("try to remove %s\n", varp->name().c_str());
			varp->unlinkFrBack();
		}
#endif
	}
	~CleanUnusedVarVisitor() = default;
};

class CleanActiveVisitor VL_NOT_FINAL : public EmitCBaseVisitor {
	size_t m_counts = 0;
	virtual void visit(AstAssignDly* nodep) override {
		m_counts++;
	}
	virtual void visit(AstActive* nodep) override {
		m_counts = 0;
		iterateChildrenConst(nodep);
		if (m_counts == 0) {
			nodep->unlinkFrBack();
			VL_DO_DANGLING(pushDeletep(nodep), nodep);
		}
	}
	virtual void visit(AstNode* nodep) override { iterateChildrenConst(nodep); }
public:
	CleanActiveVisitor(AstNodeModule* nodep)
	{
		iterate(nodep);
	}
	~CleanActiveVisitor() = default;
};

//######################################################################
// Expand state, as a visitor of each AstNode

class ExpandVisitor1 final : public VNVisitor {
private:
    // NODE STATE
    //  AstNode::user1()        -> bool.  Processed
    const VNUser1InUse m_inuser1;

    // STATE
    AstNode* m_stmtp = nullptr;  // Current statement
    VDouble0 m_statWides;  // Statistic tracking
    VDouble0 m_statWideWords;  // Statistic tracking
    VDouble0 m_statWideLimited;  // Statistic tracking

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    bool doExpand(AstNode* nodep) {
        ++m_statWides;
        if (nodep->widthWords() <= v3Global.opt.expandLimit()) {
            m_statWideWords += nodep->widthWords();
            return true;
        } else {
            ++m_statWideLimited;
            return false;
        }
    }

    static int longOrQuadWidth(AstNode* nodep) {
        return (nodep->width() + (VL_EDATASIZE - 1)) & ~(VL_EDATASIZE - 1);
    }
    static V3Number notWideMask(AstNode* nodep) {
        return V3Number(nodep, VL_EDATASIZE, ~VL_MASK_E(nodep->widthMin()));
    }
    static V3Number wordMask(AstNode* nodep) {
        if (nodep->isWide()) {
            return V3Number{nodep, VL_EDATASIZE, VL_MASK_E(nodep->widthMin())};
        } else {
            V3Number mask{nodep, longOrQuadWidth(nodep)};
            mask.setMask(nodep->widthMin());
            return mask;
        }
    }

    static void insertBefore(AstNode* placep, AstNode* newp) {
        newp->user1(1);  // Already processed, don't need to re-iterate
        VNRelinker linker;
        placep->unlinkFrBack(&linker);
        newp->addNext(placep);
        linker.relink(newp);
    }
    static void replaceWithDelete(AstNode* nodep, AstNode* newp) {
        newp->user1(1);  // Already processed, don't need to re-iterate
        nodep->replaceWith(newp);
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
    }
    static AstNode* newWordAssign(AstNodeAssign* placep, int word, AstNode* lhsp, AstNode* rhsp) {
        FileLine* const fl = placep->fileline();
        return new AstAssign{fl,
                             new AstWordSel{fl, lhsp->cloneTree(true),
                                            new AstConst{fl, static_cast<uint32_t>(word)}},
                             rhsp};
    }
    static void addWordAssign(AstNodeAssign* placep, int word, AstNode* lhsp, AstNode* rhsp) {
        insertBefore(placep, newWordAssign(placep, word, lhsp, rhsp));
    }
    static void addWordAssign(AstNodeAssign* placep, int word, AstNode* rhsp) {
        addWordAssign(placep, word, placep->lhsp(), rhsp);
    }

    static void fixCloneLvalue(AstNode* nodep) {
        // In AstSel transforms, we call clone() on VarRefs that were lvalues,
        // but are now being used on the RHS of the assignment
        if (VN_IS(nodep, VarRef)) VN_AS(nodep, VarRef)->access(VAccess::READ);
        // Iterate
        if (nodep->op1p()) fixCloneLvalue(nodep->op1p());
        if (nodep->op2p()) fixCloneLvalue(nodep->op2p());
        if (nodep->op3p()) fixCloneLvalue(nodep->op3p());
        if (nodep->op4p()) fixCloneLvalue(nodep->op4p());
    }

    static AstNode* newAstWordSelClone(AstNode* nodep, int word) {
        // Get the specified word number from a wide array
        // Or, if it's a long/quad, do appropriate conversion to wide
        // Concat may pass negative word numbers, that means it wants a zero
        FileLine* const fl = nodep->fileline();
        if (nodep->isWide() && word >= 0 && word < nodep->widthWords()) {
            return new AstWordSel{fl, nodep->cloneTree(true),
                                  new AstConst{fl, static_cast<uint32_t>(word)}};
        } else if (nodep->isQuad() && word == 0) {
            AstNode* const quadfromp = nodep->cloneTree(true);
            quadfromp->dtypeSetBitUnsized(VL_QUADSIZE, quadfromp->widthMin(), VSigning::UNSIGNED);
            return quadfromp;
        } else if (nodep->isQuad() && word == 1) {
            AstNode* const quadfromp = nodep->cloneTree(true);
            quadfromp->dtypeSetBitUnsized(VL_QUADSIZE, quadfromp->widthMin(), VSigning::UNSIGNED);
            return new AstShiftR{fl, quadfromp, new AstConst{fl, VL_EDATASIZE}, VL_EDATASIZE};
        } else if (!nodep->isWide() && !nodep->isQuad() && word == 0) {
            return nodep->cloneTree(true);
        } else {  // Out of bounds
            return new AstConst{fl, 0};
        }
    }

    static AstNode* newWordGrabShift(FileLine* fl, int word, AstNode* lhsp, int shift) {
        // Extract the expression to grab the value for the specified word, if it's the shift
        // of shift bits from lhsp
        AstNode* newp;
        // Negative word numbers requested for lhs when it's "before" what we want.
        // We get a 0 then.
        const int othword = word - shift / VL_EDATASIZE;
        AstNode* const llowp = newAstWordSelClone(lhsp, othword);
        if (const int loffset = VL_BITBIT_E(shift)) {
            AstNode* const lhip = newAstWordSelClone(lhsp, othword - 1);
            const int nbitsonright = VL_EDATASIZE - loffset;  // bits that end up in lword
            newp = new AstOr{
                fl,
                new AstAnd{fl, new AstConst{fl, AstConst::SizedEData(), VL_MASK_E(loffset)},
                           new AstShiftR{fl, lhip,
                                         new AstConst{fl, static_cast<uint32_t>(nbitsonright)},
                                         VL_EDATASIZE}},
                new AstAnd{fl, new AstConst{fl, AstConst::SizedEData(), ~VL_MASK_E(loffset)},
                           new AstShiftL{fl, llowp,
                                         new AstConst{fl, static_cast<uint32_t>(loffset)},
                                         VL_EDATASIZE}}};
        } else {
            newp = llowp;
        }
        return newp;
    }

    static AstNode* newWordSel(FileLine* fl, AstNode* fromp, AstNode* lsbp,
                               uint32_t wordOffset = 0) {
        // Return equation to get the VL_BITWORD of a constant or non-constant
        UASSERT_OBJ(fromp->isWide(), fromp, "Only need AstWordSel on wide from's");
        if (wordOffset >= static_cast<uint32_t>(fromp->widthWords())) {
            // e.g. "logic [95:0] var[0]; logic [0] sel; out = var[sel];"
            // Squash before C++ to avoid getting a C++ compiler warning
            // (even though code would be unreachable as presumably a
            // AstCondBound is protecting above this node.
            return new AstConst{fl, AstConst::SizedEData(), 0};
        } else {
            AstNode* wordp;
            FileLine* const lfl = lsbp->fileline();
            if (VN_IS(lsbp, Const)) {
                wordp = new AstConst{lfl, wordOffset + VL_BITWORD_E(VN_AS(lsbp, Const)->toUInt())};
            } else {
                wordp = new AstShiftR{lfl, lsbp->cloneTree(true),
                                      new AstConst{lfl, VL_EDATASIZE_LOG2}, VL_EDATASIZE};
                if (wordOffset
                    != 0) {  // This is indexing a arraysel, so a 32 bit constant is fine
                    wordp = new AstAdd{lfl, new AstConst{lfl, wordOffset}, wordp};
                }
            }
            return new AstWordSel{fl, fromp, wordp};
        }
    }

    static AstNode* dropCondBound(AstNode* nodep) {
        // Experimental only...
        //  If there's a CONDBOUND safety to keep arrays in bounds,
        //  we're going to AND it to a value that always fits inside a
        //  word, so we don't need it.
        // if (VN_IS(nodep, CondBound) && VN_IS(VN_AS(nodep, CondBound)->lhsp(), Lte)) {
        //    nodep = VN_AS(nodep, CondBound)->rhsp();
        //}
        return nodep;
    }

    static AstNode* newSelBitBit(AstNode* lsbp) {
        // Return equation to get the VL_BITBIT of a constant or non-constant
        FileLine* const fl = lsbp->fileline();
        if (VN_IS(lsbp, Const)) {
            return new AstConst{fl, VL_BITBIT_E(VN_AS(lsbp, Const)->toUInt())};
        } else {
            return new AstAnd{fl, new AstConst{fl, VL_EDATASIZE - 1},
                              dropCondBound(lsbp)->cloneTree(true)};
        }
    }

    //====================

    bool expandWide(AstNodeAssign* nodep, AstConst* rhsp) {
        UINFO(8, "    Wordize ASSIGN(CONST) " << nodep << endl);
        if (!doExpand(nodep)) return false;
        // -> {for each_word{ ASSIGN(WORDSEL(wide,#),WORDSEL(CONST,#))}}
        if (rhsp->num().isFourState()) {
            rhsp->v3warn(E_UNSUPPORTED,  // LCOV_EXCL_LINE  // impossible?
                         "Unsupported: 4-state numbers in this context");
        }
        FileLine* const fl = nodep->fileline();
        for (int w = 0; w < nodep->widthWords(); ++w) {
            addWordAssign(nodep, w,
                          new AstConst{fl, AstConst::SizedEData(), rhsp->num().edataWord(w)});
        }
        return true;
    }
    //-------- Uniops
    bool expandWide(AstNodeAssign* nodep, AstVarRef* rhsp) {
        UINFO(8, "    Wordize ASSIGN(VARREF) " << nodep << endl);
        if (!doExpand(nodep)) return false;
        for (int w = 0; w < nodep->widthWords(); ++w) {
            addWordAssign(nodep, w, newAstWordSelClone(rhsp, w));
        }
        return true;
    }
    bool expandWide(AstNodeAssign* nodep, AstArraySel* rhsp) {
        UINFO(8, "    Wordize ASSIGN(ARRAYSEL) " << nodep << endl);
        UASSERT_OBJ(!VN_IS(nodep->dtypep()->skipRefp(), UnpackArrayDType), nodep,
                    "ArraySel with unpacked arrays should have been removed in V3Slice");
        if (!doExpand(nodep)) return false;
        for (int w = 0; w < nodep->widthWords(); ++w) {
            addWordAssign(nodep, w, newAstWordSelClone(rhsp, w));
        }
        return true;
    }
    bool expandWide(AstNodeAssign* nodep, AstNot* rhsp) {
        UINFO(8, "    Wordize ASSIGN(NOT) " << nodep << endl);
        // -> {for each_word{ ASSIGN(WORDSEL(wide,#),NOT(WORDSEL(lhs,#))) }}
        if (!doExpand(nodep)) return false;
        FileLine* const fl = rhsp->fileline();
        for (int w = 0; w < nodep->widthWords(); ++w) {
            addWordAssign(nodep, w, new AstNot{fl, newAstWordSelClone(rhsp->lhsp(), w)});
        }
        return true;
    }
    //-------- Biops
    bool expandWide(AstNodeAssign* nodep, AstAnd* rhsp) {
        UINFO(8, "    Wordize ASSIGN(AND) " << nodep << endl);
        if (!doExpand(nodep)) return false;
        FileLine* const fl = nodep->fileline();
        for (int w = 0; w < nodep->widthWords(); ++w) {
            addWordAssign(nodep, w,
                          new AstAnd{fl, newAstWordSelClone(rhsp->lhsp(), w),
                                     newAstWordSelClone(rhsp->rhsp(), w)});
        }
        return true;
    }
    bool expandWide(AstNodeAssign* nodep, AstOr* rhsp) {
        UINFO(8, "    Wordize ASSIGN(OR) " << nodep << endl);
        if (!doExpand(nodep)) return false;
        FileLine* const fl = nodep->fileline();
        for (int w = 0; w < nodep->widthWords(); ++w) {
            addWordAssign(nodep, w,
                          new AstOr{fl, newAstWordSelClone(rhsp->lhsp(), w),
                                    newAstWordSelClone(rhsp->rhsp(), w)});
        }
        return true;
    }
    bool expandWide(AstNodeAssign* nodep, AstXor* rhsp) {
        UINFO(8, "    Wordize ASSIGN(XOR) " << nodep << endl);
        if (!doExpand(nodep)) return false;
        FileLine* const fl = nodep->fileline();
        for (int w = 0; w < nodep->widthWords(); ++w) {
            addWordAssign(nodep, w,
                          new AstXor{fl, newAstWordSelClone(rhsp->lhsp(), w),
                                     newAstWordSelClone(rhsp->rhsp(), w)});
        }
        return true;
    }
    //-------- Triops
    bool expandWide(AstNodeAssign* nodep, AstNodeCond* rhsp) {
        UINFO(8, "    Wordize ASSIGN(COND) " << nodep << endl);
        if (!doExpand(nodep)) return false;
        FileLine* const fl = nodep->fileline();
        for (int w = 0; w < nodep->widthWords(); ++w) {
            addWordAssign(nodep, w,
                          new AstCond{fl, rhsp->condp()->cloneTree(true),
                                      newAstWordSelClone(rhsp->expr1p(), w),
                                      newAstWordSelClone(rhsp->expr2p(), w)});
        }
        return true;
    }

    // VISITORS
    virtual void visit(AstExtend* nodep) override {
        if (nodep->user1SetOnce()) return;  // Process once
        iterateChildren(nodep);
        if (nodep->isWide()) {
            // See under ASSIGN(EXTEND)
        } else {
            AstNode* const lhsp = nodep->lhsp()->unlinkFrBack();
            AstNode* newp = lhsp;
            if (nodep->isQuad()) {
                if (lhsp->isQuad()) {
                    lhsp->dtypeFrom(nodep);  // Just mark it, else nop
                } else if (lhsp->isWide()) {
                    nodep->v3fatalSrc("extending larger thing into smaller?");
                }
            } else {  // Long
                UASSERT_OBJ(!(lhsp->isQuad() || lhsp->isWide()), nodep,
                            "extending larger thing into smaller?");
                lhsp->dtypeFrom(nodep);  // Just mark it, else nop
            }
            VL_DO_DANGLING(replaceWithDelete(nodep, newp), nodep);
        }
    }

    virtual void visit(AstSel* nodep) override {
        if (nodep->user1SetOnce()) return;  // Process once
        iterateChildren(nodep);
        // Remember, Sel's may have non-integer rhs, so need to optimize for that!
        UASSERT_OBJ(nodep->widthMin() == nodep->widthConst(), nodep, "Width mismatch");
        if (VN_IS(nodep->backp(), NodeAssign)
            && nodep == VN_AS(nodep->backp(), NodeAssign)->lhsp()) {
            // Sel is an LHS assignment select
        } else if (nodep->isWide()) {
            // See under ASSIGN(WIDE)
        } else if (nodep->fromp()->isWide()) {
            UINFO(8, "    SEL(wide) " << nodep << endl);
            UASSERT_OBJ(nodep->widthConst() <= 64, nodep, "Inconsistent width");
            // Selection amounts
            // Check for constant shifts & save some constification work later.
            // Grab lowest bit(s)
            FileLine* const nfl = nodep->fileline();
            FileLine* const lfl = nodep->lsbp()->fileline();
            FileLine* const ffl = nodep->fromp()->fileline();
            AstNode* lowwordp = newWordSel(ffl, nodep->fromp()->cloneTree(true), nodep->lsbp());
            AstNode* const lowp
                = new AstShiftR{nfl, lowwordp, newSelBitBit(nodep->lsbp()), nodep->width()};
            // If > 1 bit, we might be crossing the word boundary
            AstNode* midp = nullptr;
            if (nodep->widthConst() > 1) {
                const uint32_t midMsbOffset
                    = std::min<uint32_t>(nodep->widthConst(), VL_EDATASIZE) - 1;
                AstNode* const midMsbp = new AstAdd{lfl, new AstConst{lfl, midMsbOffset},
                                                    nodep->lsbp()->cloneTree(false)};
                AstNode* midwordp =  // SEL(from,[midwordnum])
                    newWordSel(ffl, nodep->fromp()->cloneTree(true), midMsbp, 0);
                // newWordSel clones the index, so delete it
                VL_DO_DANGLING(midMsbp->deleteTree(), midMsbp);
                AstNode* const midshiftp = new AstSub{lfl, new AstConst{lfl, VL_EDATASIZE},
                                                      newSelBitBit(nodep->lsbp())};
                // If we're selecting bit zero, then all 32 bits in the mid word
                // get shifted << by 32 bits, so ignore them.
                const V3Number zero{nodep, longOrQuadWidth(nodep)};
                midp = new AstCond{
                    nfl,
                    // lsb % VL_EDATASIZE == 0 ?

                    new AstEq{nfl, new AstConst{nfl, 0}, newSelBitBit(nodep->lsbp())},
                    // 0 :
                    new AstConst{nfl, zero},
                    //  midword >> (VL_EDATASIZE - (lbs % VL_EDATASIZE))
                    new AstShiftL{nfl, midwordp, midshiftp, nodep->width()}};
            }
            // If > 32 bits, we might be crossing the second word boundary
            AstNode* hip = nullptr;
            if (nodep->widthConst() > VL_EDATASIZE) {
                const uint32_t hiMsbOffset = nodep->widthConst() - 1;
                AstNode* const hiMsbp = new AstAdd{lfl, new AstConst{lfl, hiMsbOffset},
                                                   nodep->lsbp()->cloneTree(false)};
                AstNode* hiwordp =  // SEL(from,[hiwordnum])
                    newWordSel(ffl, nodep->fromp()->cloneTree(true), hiMsbp);
                // newWordSel clones the index, so delete it
                VL_DO_DANGLING(hiMsbp->deleteTree(), hiMsbp);
                AstNode* const hishiftp = new AstCond{
                    nfl,
                    // lsb % VL_EDATASIZE == 0 ?
                    new AstEq{nfl, new AstConst{nfl, 0}, newSelBitBit(nodep->lsbp())},
                    // VL_EDATASIZE :
                    new AstConst{lfl, VL_EDATASIZE},
                    // 64 - (lbs % VL_EDATASIZE)
                    new AstSub{lfl, new AstConst{lfl, 64}, newSelBitBit(nodep->lsbp())}};
                hip = new AstShiftL{nfl, hiwordp, hishiftp, nodep->width()};
            }

            AstNode* newp = lowp;
            if (midp) newp = new AstOr{nfl, midp, newp};
            if (hip) newp = new AstOr{nfl, hip, newp};
            newp->dtypeFrom(nodep);
            VL_DO_DANGLING(replaceWithDelete(nodep, newp), nodep);
        } else {  // Long/Quad from Long/Quad
            UINFO(8, "    SEL->SHIFT " << nodep << endl);
            FileLine* const fl = nodep->fileline();
            AstNode* fromp = nodep->fromp()->unlinkFrBack();
            AstNode* const lsbp = nodep->lsbp()->unlinkFrBack();
            if (const AstConst* const constp = VN_AS(lsbp, Const)) {
                const V3Number& num = constp->num();
                if (num.isEqZero()) {
                    // Special Case, discard right shift 0 bits
                    VL_DO_DANGLING(lsbp->deleteTree(), lsbp);
                    VL_DO_DANGLING(replaceWithDelete(nodep, fromp), nodep);
                    return;
                }
            }
            // {large}>>32 requires 64-bit shift operation; then cast
            auto newp = new AstShiftR{fl, fromp, dropCondBound(lsbp), fromp->width()};
            newp->dtypeFrom(fromp);
            newp->dtypeFrom(nodep);
            VL_DO_DANGLING(replaceWithDelete(nodep, newp), nodep);
        }
    }

    bool expandWide(AstNodeAssign* nodep, AstSel* rhsp) {
        UASSERT_OBJ(nodep->widthMin() == rhsp->widthConst(), nodep, "Width mismatch");
        if (!doExpand(nodep)) return false;
        if (VN_IS(rhsp->lsbp(), Const) && VL_BITBIT_E(rhsp->lsbConst()) == 0) {
            const int lsb = rhsp->lsbConst();
            UINFO(8, "    Wordize ASSIGN(SEL,align) " << nodep << endl);
            for (int w = 0; w < nodep->widthWords(); ++w) {
                addWordAssign(nodep, w, newAstWordSelClone(rhsp->fromp(), w + VL_BITWORD_E(lsb)));
            }
            return true;
        } else {
            UINFO(8, "    Wordize ASSIGN(EXTRACT,misalign) " << nodep << endl);
            FileLine* const nfl = nodep->fileline();
            FileLine* const rfl = rhsp->fileline();
            FileLine* const ffl = rhsp->fromp()->fileline();
            FileLine* const lfl = rhsp->lsbp()->fileline();
            for (int w = 0; w < nodep->widthWords(); ++w) {
                // Grab lowest bits
                AstNode* const lowwordp
                    = newWordSel(rfl, rhsp->fromp()->cloneTree(true), rhsp->lsbp(), w);
                AstNode* const lowp
                    = new AstShiftR{rfl, lowwordp, newSelBitBit(rhsp->lsbp()), VL_EDATASIZE};
                // Upper bits
                const V3Number zero{nodep, VL_EDATASIZE, 0};
                AstNode* const midwordp =  // SEL(from,[1+wordnum])
                    newWordSel(ffl, rhsp->fromp()->cloneTree(true), rhsp->lsbp(), w + 1);
                AstNode* const midshiftp
                    = new AstSub{lfl, new AstConst{lfl, VL_EDATASIZE}, newSelBitBit(rhsp->lsbp())};
                AstNode* const midmayp = new AstShiftL{rfl, midwordp, midshiftp, VL_EDATASIZE};
                AstNode* const midp = new AstCond{
                    rfl, new AstEq{rfl, new AstConst{rfl, 0}, newSelBitBit(rhsp->lsbp())},
                    new AstConst{rfl, zero}, midmayp};
                AstNode* const newp = new AstOr{nfl, midp, lowp};
                addWordAssign(nodep, w, newp);
            }
            return true;
        }
    }

    bool expandLhs(AstNodeAssign* nodep, AstSel* lhsp) {
        // Possibilities
        //      destp: wide or narrow
        //      rhsp:  wide (destp must be wide), narrow, or 1 bit wide
        //      rhsp:  may be allones and can remove AND NOT gate
        //      lsbp:  constant or variable
        // Yuk.
        FileLine* const nfl = nodep->fileline();
        FileLine* const lfl = lhsp->fileline();
        const bool destwide = lhsp->fromp()->isWide();
        const bool ones = nodep->rhsp()->isAllOnesV();
        if (VN_IS(lhsp->lsbp(), Const)) {
            // The code should work without this constant test, but it won't
            // constify as nicely as we'd like.
            AstNode* rhsp = nodep->rhsp()->unlinkFrBack();
            AstNode* const destp = lhsp->fromp()->unlinkFrBack();
            const int lsb = lhsp->lsbConst();
            const int msb = lhsp->msbConst();
            V3Number maskset{nodep, destp->widthMin()};
            for (int bit = lsb; bit < (msb + 1); bit++) maskset.setBit(bit, 1);
            V3Number maskold{nodep, destp->widthMin()};
            maskold.opNot(maskset);
            if (destwide) {
                UINFO(8, "    ASSIGNSEL(const,wide) " << nodep << endl);
                for (int w = 0; w < destp->widthWords(); ++w) {
                    if (w >= VL_BITWORD_E(lsb) && w <= VL_BITWORD_E(msb)) {
                        // else we would just be setting it to the same exact value
                        AstNode* oldvalp = newAstWordSelClone(destp, w);
                        fixCloneLvalue(oldvalp);
                        if (!ones) {
                            oldvalp = new AstAnd{
                                lfl,
                                new AstConst{lfl, AstConst::SizedEData(), maskold.edataWord(w)},
                                oldvalp};
                        }

                        // Appropriate word of new value to insert:
                        AstNode* newp = newWordGrabShift(lfl, w, rhsp, lsb);

                        // Apply cleaning at the top word of the destination
                        // (no cleaning to do if dst's width is a whole number
                        // of words).
                        if (w == destp->widthWords() - 1 && VL_BITBIT_E(destp->widthMin()) != 0) {
                            V3Number cleanmask{nodep, VL_EDATASIZE};
                            cleanmask.setMask(VL_BITBIT_E(destp->widthMin()));
                            newp = new AstAnd{lfl, newp, new AstConst{lfl, cleanmask}};
                        }

                        addWordAssign(nodep, w, destp, new AstOr{lfl, oldvalp, newp});
                    }
                }
                VL_DO_DANGLING(rhsp->deleteTree(), rhsp);
                VL_DO_DANGLING(destp->deleteTree(), destp);
            } else {
                UINFO(8, "    ASSIGNSEL(const,narrow) " << nodep << endl);
                AstNode* oldvalp = destp->cloneTree(true);
                fixCloneLvalue(oldvalp);
                if (!ones) { oldvalp = new AstAnd{lfl, new AstConst{lfl, maskold}, oldvalp}; }

                // The bit-select can refer to bits outside the width of nodep
                // which we aren't allowed to assign to.  This is a mask of the
                // valid range of nodep which we apply to the new shifted RHS.
                V3Number cleanmask{nodep, destp->widthMin()};
                cleanmask.setMask(destp->widthMin());
                AstNode* const shifted = new AstShiftL{
                    lfl, rhsp, new AstConst{lfl, static_cast<uint32_t>(lsb)}, destp->width()};
                AstNode* const cleaned = new AstAnd{lfl, shifted, new AstConst{lfl, cleanmask}};
                AstNode* const newp = new AstAssign{nfl, destp, new AstOr{lfl, oldvalp, cleaned}};
                insertBefore(nodep, newp);
            }
            return true;
        } else {  // non-const select offset
            if (destwide && lhsp->widthConst() == 1) {
                UINFO(8, "    ASSIGNSEL(varlsb,wide,1bit) " << nodep << endl);
                AstNode* const rhsp = nodep->rhsp()->unlinkFrBack();
                AstNode* const destp = lhsp->fromp()->unlinkFrBack();
                AstNode* oldvalp = newWordSel(lfl, destp->cloneTree(true), lhsp->lsbp());
                fixCloneLvalue(oldvalp);
                if (!ones) {
                    oldvalp = new AstAnd{
                        lfl,
                        new AstNot{
                            lfl, new AstShiftL{lfl, new AstConst{nfl, 1},
                                               // newSelBitBit may exceed the MSB of this variable.
                                               // That's ok as we'd just AND with a larger value,
                                               // but oldval would clip the upper bits to sanity
                                               newSelBitBit(lhsp->lsbp()), VL_EDATASIZE}},
                        oldvalp};
                }
                // Restrict the shift amount to 0-31, see bug804.
                AstNode* const shiftp = new AstAnd{nfl, lhsp->lsbp()->cloneTree(true),
                                                   new AstConst{nfl, VL_EDATASIZE - 1}};
                AstNode* const newp = new AstAssign{
                    nfl, newWordSel(nfl, destp, lhsp->lsbp()),
                    new AstOr{lfl, oldvalp, new AstShiftL{lfl, rhsp, shiftp, VL_EDATASIZE}}};
                insertBefore(nodep, newp);
                return true;
            } else if (destwide) {
                UINFO(8, "    ASSIGNSEL(varlsb,wide) -- NoOp -- " << nodep << endl);
                //   For wide destp, we can either form a equation for every destination word,
                // with the appropriate long equation of if it's being written or not.
                //   Or, we can use a LHS variable arraysel with
                //   non-constant index to set the vector.
                // Doing the variable arraysel is better for globals and large arrays,
                // doing every word is better for temporaries and if we're setting most words
                // since it may result in better substitution optimizations later.
                //   This results in so much code, we're better off leaving a function call.
                // Reconsider if we get subexpression elimination.
                return false;
            } else {
                UINFO(8, "    ASSIGNSEL(varlsb,narrow) " << nodep << endl);
                // nodep->dumpTree(cout, "-  old: ");
                AstNode* rhsp = nodep->rhsp()->unlinkFrBack();
                AstNode* const destp = lhsp->fromp()->unlinkFrBack();
                AstNode* oldvalp = destp->cloneTree(true);
                fixCloneLvalue(oldvalp);

                V3Number maskwidth{nodep, destp->widthMin()};
                for (int bit = 0; bit < lhsp->widthConst(); bit++) maskwidth.setBit(bit, 1);

                if (!ones) {
                    oldvalp = new AstAnd{
                        lfl,
                        new AstNot{lfl,
                                   new AstShiftL{lfl, new AstConst{nfl, maskwidth},
                                                 lhsp->lsbp()->cloneTree(true), destp->width()}},
                        oldvalp};
                }
                AstNode* newp
                    = new AstShiftL{lfl, rhsp, lhsp->lsbp()->cloneTree(true), destp->width()};
                // Apply cleaning to the new value being inserted.  Mask is
                // slightly wider than necessary to avoid an AND with all ones
                // being optimized out.  No need to clean if destp is
                // quad-sized as there are no extra bits to contaminate
                if (destp->widthMin() != 64) {
                    V3Number cleanmask{nodep, destp->widthMin() + 1};
                    cleanmask.setMask(destp->widthMin());
                    newp = new AstAnd{lfl, newp, new AstConst{lfl, cleanmask}};
                }

                newp = new AstAssign{nfl, destp, new AstOr{lfl, oldvalp, newp}};
                // newp->dumpTree(cout, "-  new: ");
                insertBefore(nodep, newp);
                return true;
            }
        }
    }

    virtual void visit(AstConcat* nodep) override {
        if (nodep->user1SetOnce()) return;  // Process once
        iterateChildren(nodep);
        if (nodep->isWide()) {
            // See under ASSIGN(WIDE)
        } else {
            UINFO(8, "    CONCAT " << nodep << endl);
            FileLine* const fl = nodep->fileline();
            AstNode* lhsp = nodep->lhsp()->unlinkFrBack();
            AstNode* rhsp = nodep->rhsp()->unlinkFrBack();
            const uint32_t rhsshift = rhsp->widthMin();
            AstNode* const newp = new AstOr{
                fl, new AstShiftL{fl, lhsp, new AstConst{fl, rhsshift}, nodep->width()}, rhsp};
            newp->dtypeFrom(nodep);  // Unsigned
            VL_DO_DANGLING(replaceWithDelete(nodep, newp), nodep);
        }
    }
    bool expandWide(AstNodeAssign* nodep, AstConcat* rhsp) {
        UINFO(8, "    Wordize ASSIGN(CONCAT) " << nodep << endl);
        if (!doExpand(rhsp)) return false;
        FileLine* const fl = rhsp->fileline();
        // Lhs or Rhs may be word, long, or quad.
        // newAstWordSelClone nicely abstracts the difference.
        const int rhsshift = rhsp->rhsp()->widthMin();
        // Sometimes doing the words backwards is preferable.
        // When we have x={x,foo} backwards is better, when x={foo,x} forward is better
        // However V3Subst tends to rip this up, so not worth optimizing now.
        for (int w = 0; w < rhsp->widthWords(); ++w) {
            addWordAssign(nodep, w,
                          new AstOr{fl, newWordGrabShift(fl, w, rhsp->lhsp(), rhsshift),
                                    newAstWordSelClone(rhsp->rhsp(), w)});
        }
        return true;
    }

    virtual void visit(AstReplicate* nodep) override {
        if (nodep->user1SetOnce()) return;  // Process once
        iterateChildren(nodep);
        if (nodep->isWide()) {
            // See under ASSIGN(WIDE)
        } else {
            FileLine* const fl = nodep->fileline();
            AstNode* lhsp = nodep->lhsp()->unlinkFrBack();
            AstNode* newp;
            const int lhswidth = lhsp->widthMin();
            if (lhswidth == 1) {
                UINFO(8, "    REPLICATE(w1) " << nodep << endl);
                newp = new AstNegate{fl, lhsp};
            } else {
                UINFO(8, "    REPLICATE " << nodep << endl);
                const AstConst* const constp = VN_AS(nodep->rhsp(), Const);
                UASSERT_OBJ(constp, nodep,
                            "Replication value isn't a constant.  Checked earlier!");
                const uint32_t times = constp->toUInt();
                newp = lhsp->cloneTree(true);
                for (unsigned repnum = 1; repnum < times; repnum++) {
                    const int rhsshift = repnum * lhswidth;
                    newp = new AstOr{
                        fl,
                        new AstShiftL{fl, lhsp->cloneTree(true),
                                      new AstConst{fl, static_cast<uint32_t>(rhsshift)},
                                      nodep->width()},
                        newp};
                    newp->dtypeFrom(nodep);  // Unsigned
                }
                VL_DO_DANGLING(lhsp->deleteTree(), lhsp);  // Never used
            }
            newp->dtypeFrom(nodep);  // Unsigned
            VL_DO_DANGLING(replaceWithDelete(nodep, newp), nodep);
        }
    }
    bool expandWide(AstNodeAssign* nodep, AstReplicate* rhsp) {
        UINFO(8, "    Wordize ASSIGN(REPLICATE) " << nodep << endl);
        if (!doExpand(rhsp)) return false;
        FileLine* const fl = nodep->fileline();
        AstNode* const lhsp = rhsp->lhsp();
        const int lhswidth = lhsp->widthMin();
        const AstConst* const constp = VN_AS(rhsp->rhsp(), Const);
        UASSERT_OBJ(constp, rhsp, "Replication value isn't a constant.  Checked earlier!");
        const uint32_t times = constp->toUInt();
        for (int w = 0; w < rhsp->widthWords(); ++w) {
            AstNode* newp;
            if (lhswidth == 1) {
                newp = new AstNegate{fl, lhsp->cloneTree(true)};
                // Replicate always unsigned
                newp->dtypeSetLogicSized(VL_EDATASIZE, VSigning::UNSIGNED);
            } else {
                newp = newAstWordSelClone(lhsp, w);
                FileLine* const rfl = rhsp->fileline();
                for (unsigned repnum = 1; repnum < times; repnum++) {
                    newp = new AstOr{fl, newWordGrabShift(rfl, w, lhsp, lhswidth * repnum), newp};
                }
            }
            addWordAssign(nodep, w, newp);
        }
        return true;
    }

    void visitEqNeq(AstNodeBiop* nodep) {
        if (nodep->user1SetOnce()) return;  // Process once
        iterateChildren(nodep);
        if (nodep->lhsp()->isWide()) {
            UINFO(8, "    Wordize EQ/NEQ " << nodep << endl);
            // -> (0=={or{for each_word{WORDSEL(lhs,#)^WORDSEL(rhs,#)}}}
            FileLine* const fl = nodep->fileline();
            AstNode* newp = nullptr;
            for (int w = 0; w < nodep->lhsp()->widthWords(); ++w) {
                AstNode* const eqp = new AstXor{fl, newAstWordSelClone(nodep->lhsp(), w),
                                                newAstWordSelClone(nodep->rhsp(), w)};
                newp = newp ? new AstOr{fl, newp, eqp} : eqp;
            }
            if (VN_IS(nodep, Neq)) {
                newp = new AstNeq{fl, new AstConst{fl, AstConst::SizedEData(), 0}, newp};
            } else {
                newp = new AstEq{fl, new AstConst{fl, AstConst::SizedEData(), 0}, newp};
            }
            VL_DO_DANGLING(replaceWithDelete(nodep, newp), nodep);
        }
    }
    virtual void visit(AstEq* nodep) override { visitEqNeq(nodep); }
    virtual void visit(AstNeq* nodep) override { visitEqNeq(nodep); }

    virtual void visit(AstRedOr* nodep) override {
        if (nodep->user1SetOnce()) return;  // Process once
        iterateChildren(nodep);
        FileLine* const fl = nodep->fileline();
        if (nodep->lhsp()->isWide()) {
            UINFO(8, "    Wordize REDOR " << nodep << endl);
            // -> (0!={or{for each_word{WORDSEL(lhs,#)}}}
            AstNode* newp = nullptr;
            for (int w = 0; w < nodep->lhsp()->widthWords(); ++w) {
                AstNode* const eqp = newAstWordSelClone(nodep->lhsp(), w);
                newp = newp ? new AstOr{fl, newp, eqp} : eqp;
            }
            newp = new AstNeq{fl, new AstConst{fl, AstConst::SizedEData(), 0}, newp};
            VL_DO_DANGLING(replaceWithDelete(nodep, newp), nodep);
        } else {
            UINFO(8, "    REDOR->EQ " << nodep << endl);
            AstNode* const lhsp = nodep->lhsp()->unlinkFrBack();
            AstNode* const newp = new AstNeq{
                fl, new AstConst{fl, AstConst::WidthedValue(), longOrQuadWidth(nodep), 0}, lhsp};
            VL_DO_DANGLING(replaceWithDelete(nodep, newp), nodep);
        }
    }
    virtual void visit(AstRedAnd* nodep) override {
        if (nodep->user1SetOnce()) return;  // Process once
        iterateChildren(nodep);
        FileLine* const fl = nodep->fileline();
        if (nodep->lhsp()->isWide()) {
            UINFO(8, "    Wordize REDAND " << nodep << endl);
            // -> (0!={and{for each_word{WORDSEL(lhs,#)}}}
            AstNode* newp = nullptr;
            for (int w = 0; w < nodep->lhsp()->widthWords(); ++w) {
                AstNode* eqp = newAstWordSelClone(nodep->lhsp(), w);
                if (w == nodep->lhsp()->widthWords() - 1) {
                    // Rather than doing a (slowish) ==##, we OR in the
                    // bits that aren't part of the mask
                    eqp = new AstOr{fl, new AstConst{fl, notWideMask(nodep->lhsp())},
                                    // Bug in cppcheck
                                    // cppcheck-suppress memleak
                                    eqp};
                }
                newp = newp ? new AstAnd{fl, newp, eqp} : eqp;
            }
            newp = new AstEq{fl, new AstConst{fl, AstConst::SizedEData(), VL_MASK_E(VL_EDATASIZE)},
                             newp};
            VL_DO_DANGLING(replaceWithDelete(nodep, newp), nodep);
        } else {
            UINFO(8, "    REDAND->EQ " << nodep << endl);
            AstNode* const lhsp = nodep->lhsp()->unlinkFrBack();
            AstNode* const newp = new AstEq{fl, new AstConst{fl, wordMask(lhsp)}, lhsp};
            VL_DO_DANGLING(replaceWithDelete(nodep, newp), nodep);
        }
    }
    virtual void visit(AstRedXor* nodep) override {
        if (nodep->user1SetOnce()) return;  // Process once
        iterateChildren(nodep);
        if (nodep->lhsp()->isWide()) {
            UINFO(8, "    Wordize REDXOR " << nodep << endl);
            // -> (0!={redxor{for each_word{XOR(WORDSEL(lhs,#))}}}
            FileLine* const fl = nodep->fileline();
            AstNode* newp = nullptr;
            for (int w = 0; w < nodep->lhsp()->widthWords(); ++w) {
                AstNode* const eqp = newAstWordSelClone(nodep->lhsp(), w);
                newp = newp ? new AstXor{fl, newp, eqp} : eqp;
            }
            newp = new AstRedXor{fl, newp};
            UINFO(8, "    Wordize REDXORnew " << newp << endl);
            VL_DO_DANGLING(replaceWithDelete(nodep, newp), nodep);
        }
        // We don't reduce non-wide XORs, as its more efficient to use a temp register,
        // which the inlined function does nicely.
    }

    virtual void visit(AstNodeStmt* nodep) override {
        if (nodep->user1SetOnce()) return;  // Process once
        if (!nodep->isStatement()) {
            iterateChildren(nodep);
            return;
        }
        m_stmtp = nodep;
        iterateChildren(nodep);
        m_stmtp = nullptr;
    }
    virtual void visit(AstNodeAssign* nodep) override {
        if (nodep->user1SetOnce()) return;  // Process once
        m_stmtp = nodep;
        iterateChildren(nodep);
        bool did = false;
        if (nodep->isWide() && ((VN_IS(nodep->lhsp(), VarRef) || VN_IS(nodep->lhsp(), ArraySel)))
            && ((VN_IS(nodep->lhsp(), VarRef) || VN_IS(nodep->lhsp(), ArraySel)))
            && !AstVar::scVarRecurse(nodep->lhsp())  // Need special function for SC
            && !AstVar::scVarRecurse(nodep->rhsp())) {
            if (AstConst* const rhsp = VN_CAST(nodep->rhsp(), Const)) {
                did = expandWide(nodep, rhsp);
            } else if (AstVarRef* const rhsp = VN_CAST(nodep->rhsp(), VarRef)) {
                did = expandWide(nodep, rhsp);
            } else if (AstSel* const rhsp = VN_CAST(nodep->rhsp(), Sel)) {
                did = expandWide(nodep, rhsp);
            } else if (AstArraySel* const rhsp = VN_CAST(nodep->rhsp(), ArraySel)) {
                did = expandWide(nodep, rhsp);
            } else if (AstConcat* const rhsp = VN_CAST(nodep->rhsp(), Concat)) {
                did = expandWide(nodep, rhsp);
            } else if (AstReplicate* const rhsp = VN_CAST(nodep->rhsp(), Replicate)) {
                did = expandWide(nodep, rhsp);
            } else if (AstAnd* const rhsp = VN_CAST(nodep->rhsp(), And)) {
                did = expandWide(nodep, rhsp);
            } else if (AstOr* const rhsp = VN_CAST(nodep->rhsp(), Or)) {
                did = expandWide(nodep, rhsp);
            } else if (AstNot* const rhsp = VN_CAST(nodep->rhsp(), Not)) {
                did = expandWide(nodep, rhsp);
            } else if (AstXor* const rhsp = VN_CAST(nodep->rhsp(), Xor)) {
                did = expandWide(nodep, rhsp);
            } else if (AstNodeCond* const rhsp = VN_CAST(nodep->rhsp(), NodeCond)) {
                did = expandWide(nodep, rhsp);
            }
        } else if (AstSel* const lhsp = VN_CAST(nodep->lhsp(), Sel)) {
            did = expandLhs(nodep, lhsp);
        }
        // Cleanup common code
        if (did) VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
        m_stmtp = nullptr;
    }

    //--------------------
    virtual void visit(AstVar*) override {}  // Don't hit varrefs under vars
    virtual void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit ExpandVisitor1(AstNodeModule* nodep) { iterate(nodep); }
    virtual ~ExpandVisitor1() override {
        V3Stats::addStat("Optimizations, expand wides", m_statWides);
        V3Stats::addStat("Optimizations, expand wide words", m_statWideWords);
        V3Stats::addStat("Optimizations, expand limited", m_statWideLimited);
    }
};

//######################################################################
// Clean state, as a visitor of each AstNode

class CleanVisitor final : public VNVisitor {
private:
    // NODE STATE
    // Entire netlist:
    //  AstNode::user()         -> CleanState.  For this node, 0==UNKNOWN
    //  AstNode::user2()        -> bool.  True indicates widthMin has been propagated
    //  AstNodeDType::user3()   -> AstNodeDType*.  Alternative node with C size
    const VNUser1InUse m_inuser1;
    const VNUser2InUse m_inuser2;
    const VNUser3InUse m_inuser3;

    // TYPES
    enum CleanState : uint8_t { CS_UNKNOWN, CS_CLEAN, CS_DIRTY };

    // STATE
    const AstNodeModule* m_modp = nullptr;

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    // Width resetting
    int cppWidth(AstNode* nodep) {
        if (nodep->width() <= VL_IDATASIZE) {
            return VL_IDATASIZE;
        } else if (nodep->width() <= VL_QUADSIZE) {
            return VL_QUADSIZE;
        } else {
            return nodep->widthWords() * VL_EDATASIZE;
        }
    }
    void setCppWidth(AstNode* nodep) {
        nodep->user2(true);  // Don't resize it again
        AstNodeDType* const old_dtypep = nodep->dtypep();
        const int width = cppWidth(nodep);  // widthMin is unchanged
        if (old_dtypep->width() != width) {
            // Since any given dtype's cppWidth() is the same, we can just
            // remember one conversion for each, and reuse it
            if (AstNodeDType* const new_dtypep = VN_CAST(old_dtypep->user3p(), NodeDType)) {
                nodep->dtypep(new_dtypep);
            } else {
                nodep->dtypeChgWidth(width, nodep->widthMin());
                AstNodeDType* const new_dtypep2 = nodep->dtypep();
                UASSERT_OBJ(new_dtypep2 != old_dtypep, nodep,
                            "Dtype didn't change when width changed");
                old_dtypep->user3p(new_dtypep2);  // Remember for next time
            }
        }
    }
    void computeCppWidth(AstNode* nodep) {
        if (!nodep->user2() && nodep->hasDType()) {
            if (VN_IS(nodep, Var)
                || VN_IS(nodep, NodeDType)  // Don't want to change variable widths!
                || VN_IS(nodep->dtypep()->skipRefp(), AssocArrayDType)  // Or arrays
                || VN_IS(nodep->dtypep()->skipRefp(), DynArrayDType)
                || VN_IS(nodep->dtypep()->skipRefp(), ClassRefDType)
                || VN_IS(nodep->dtypep()->skipRefp(), QueueDType)
                || VN_IS(nodep->dtypep()->skipRefp(), UnpackArrayDType)
                || VN_IS(nodep->dtypep()->skipRefp(), VoidDType)) {
            } else {
                setCppWidth(nodep);
            }
        }
    }

    // Store the clean state in the userp on each node
    void setCleanState(AstNode* nodep, CleanState clean) { nodep->user1(clean); }
    CleanState getCleanState(AstNode* nodep) { return static_cast<CleanState>(nodep->user1()); }
    bool isClean(AstNode* nodep) {
        const CleanState clstate = getCleanState(nodep);
        if (clstate == CS_CLEAN) return true;
        if (clstate == CS_DIRTY) return false;
        nodep->v3fatalSrc("Unknown clean state on node: " + nodep->prettyTypeName());
        return false;
    }
    void setClean(AstNode* nodep, bool isClean) {
        computeCppWidth(nodep);  // Just to be sure it's in widthMin
        const bool wholeUint
            = (nodep->widthMin() == VL_IDATASIZE || nodep->widthMin() == VL_QUADSIZE
               || (nodep->widthMin() % VL_EDATASIZE) == 0);
        setCleanState(nodep, ((isClean || wholeUint) ? CS_CLEAN : CS_DIRTY));
    }

    // Operate on nodes
    void insertClean(AstNode* nodep) {  // We'll insert ABOVE passed node
        UINFO(4, "  NeedClean " << nodep << endl);
        VNRelinker relinkHandle;
        nodep->unlinkFrBack(&relinkHandle);
        //
        computeCppWidth(nodep);
        V3Number mask(nodep, cppWidth(nodep));
        mask.setMask(nodep->widthMin());
        AstNode* const cleanp
            = new AstAnd(nodep->fileline(), new AstConst(nodep->fileline(), mask), nodep);
        cleanp->dtypeFrom(nodep);  // Otherwise the AND normally picks LHS
        relinkHandle.relink(cleanp);
    }
    void ensureClean(AstNode* nodep) {
        computeCppWidth(nodep);
        if (!isClean(nodep)) insertClean(nodep);
    }
    void ensureCleanAndNext(AstNode* nodep) {
        // Editing list, careful looping!
        for (AstNode* exprp = nodep; exprp;) {
            AstNode* const nextp = exprp->nextp();
            ensureClean(exprp);
            exprp = nextp;
        }
    }

    // Base type handling methods
    void operandBiop(AstNodeBiop* nodep) {
        iterateChildren(nodep);
        computeCppWidth(nodep);
        if (nodep->cleanLhs()) ensureClean(nodep->lhsp());
        if (nodep->cleanRhs()) ensureClean(nodep->rhsp());
        // no setClean.. must do it in each user routine.
    }
    void operandTriop(AstNodeTriop* nodep) {
        iterateChildren(nodep);
        computeCppWidth(nodep);
        if (nodep->cleanLhs()) ensureClean(nodep->lhsp());
        if (nodep->cleanRhs()) ensureClean(nodep->rhsp());
        if (nodep->cleanThs()) ensureClean(nodep->thsp());
        // no setClean.. must do it in each user routine.
    }
    void operandQuadop(AstNodeQuadop* nodep) {
        iterateChildren(nodep);
        computeCppWidth(nodep);
        if (nodep->cleanLhs()) ensureClean(nodep->lhsp());
        if (nodep->cleanRhs()) ensureClean(nodep->rhsp());
        if (nodep->cleanThs()) ensureClean(nodep->thsp());
        if (nodep->cleanFhs()) ensureClean(nodep->fhsp());
        // no setClean.. must do it in each user routine.
    }

    // VISITORS
    virtual void visit(AstNodeModule* nodep) override {
        VL_RESTORER(m_modp);
        {
            m_modp = nodep;
            iterateChildren(nodep);
        }
    }
    virtual void visit(AstNodeUniop* nodep) override {
        iterateChildren(nodep);
        computeCppWidth(nodep);
        if (nodep->cleanLhs()) ensureClean(nodep->lhsp());
        setClean(nodep, nodep->cleanOut());
    }
    virtual void visit(AstNodeBiop* nodep) override {
        operandBiop(nodep);
        setClean(nodep, nodep->cleanOut());
    }
    virtual void visit(AstAnd* nodep) override {
        operandBiop(nodep);
        setClean(nodep, isClean(nodep->lhsp()) || isClean(nodep->rhsp()));
    }
    virtual void visit(AstXor* nodep) override {
        operandBiop(nodep);
        setClean(nodep, isClean(nodep->lhsp()) && isClean(nodep->rhsp()));
    }
    virtual void visit(AstOr* nodep) override {
        operandBiop(nodep);
        setClean(nodep, isClean(nodep->lhsp()) && isClean(nodep->rhsp()));
    }
    virtual void visit(AstNodeQuadop* nodep) override {
        operandQuadop(nodep);
        setClean(nodep, nodep->cleanOut());
    }
    virtual void visit(AstNodeMath* nodep) override {
        iterateChildren(nodep);
        computeCppWidth(nodep);
        setClean(nodep, nodep->cleanOut());
    }
    virtual void visit(AstNodeAssign* nodep) override {
        iterateChildren(nodep);
        computeCppWidth(nodep);
        if (nodep->cleanRhs()) ensureClean(nodep->rhsp());
    }
    virtual void visit(AstText* nodep) override {  //
        setClean(nodep, true);
    }
    virtual void visit(AstScopeName* nodep) override {  //
        setClean(nodep, true);
    }
    virtual void visit(AstCNew* nodep) override {
        iterateChildren(nodep);
        setClean(nodep, true);
    }
    virtual void visit(AstSel* nodep) override {
        operandTriop(nodep);
        setClean(nodep, nodep->cleanOut());
    }
    virtual void visit(AstUCFunc* nodep) override {
        iterateChildren(nodep);
        computeCppWidth(nodep);
        setClean(nodep, false);
        // We always clean, as we don't trust those pesky users.
        if (!VN_IS(nodep->backp(), And)) insertClean(nodep);
        ensureCleanAndNext(nodep->bodysp());
    }
    virtual void visit(AstTraceDecl* nodep) override {
        // No cleaning, or would loose pointer to enum
        iterateChildren(nodep);
    }
    virtual void visit(AstTraceInc* nodep) override {
        iterateChildren(nodep);
        ensureCleanAndNext(nodep->valuep());
    }
    virtual void visit(AstTypedef* nodep) override {
        // No cleaning, or would loose pointer to enum
        iterateChildren(nodep);
    }
    virtual void visit(AstParamTypeDType* nodep) override {
        // No cleaning, or would loose pointer to enum
        iterateChildren(nodep);
    }

    // Control flow operators
    virtual void visit(AstNodeCond* nodep) override {
        iterateChildren(nodep);
        ensureClean(nodep->condp());
        setClean(nodep, isClean(nodep->expr1p()) && isClean(nodep->expr2p()));
    }
    virtual void visit(AstWhile* nodep) override {
        iterateChildren(nodep);
        ensureClean(nodep->condp());
    }
    virtual void visit(AstNodeIf* nodep) override {
        iterateChildren(nodep);
        ensureClean(nodep->condp());
    }
    virtual void visit(AstSFormatF* nodep) override {
        iterateChildren(nodep);
        ensureCleanAndNext(nodep->exprsp());
        setClean(nodep, true);  // generates a string, so not relevant
    }
    virtual void visit(AstUCStmt* nodep) override {
        iterateChildren(nodep);
        ensureCleanAndNext(nodep->bodysp());
    }
    virtual void visit(AstNodeCCall* nodep) override {
        iterateChildren(nodep);
        ensureCleanAndNext(nodep->argsp());
        setClean(nodep, true);
    }
    virtual void visit(AstCMethodHard* nodep) override {
        iterateChildren(nodep);
        ensureCleanAndNext(nodep->pinsp());
        setClean(nodep, true);
    }
    virtual void visit(AstWith* nodep) override {
        iterateChildren(nodep);
        ensureCleanAndNext(nodep->exprp());
        setClean(nodep, true);
    }
    virtual void visit(AstIntfRef* nodep) override {
        iterateChildren(nodep);
        setClean(nodep, true);  // generates a string, so not relevant
    }

    //--------------------
    // Default: Just iterate
    virtual void visit(AstNode* nodep) override {
        iterateChildren(nodep);
        computeCppWidth(nodep);
    }

public:
    // CONSTRUCTORS
    explicit CleanVisitor(AstNodeModule* nodep) { iterate(nodep); }
    virtual ~CleanVisitor() override = default;
};

class CFuncTracter final : public VNVisitor
{
    std::string m_name;
    virtual void visit(AstCFunc* nodep) override
    {
        if (nodep->name() == m_name) {
            V3EmitV::verilogForTree(nodep->stmtsp(), std::cout);
            #if 0
            nodep->dumpTree(std::cout, "trace: ", 30);
            #endif
        }
    }
    virtual void visit(AstNode* nodep) override { iterateChildren(nodep); }
public:
    // CONSTRUCTORS
    explicit CFuncTracter(AstNetlist* nodep, const std::string& name)
        : m_name(name)
    {
        iterate(nodep);
    }
    virtual ~CFuncTracter() override = default;
};

//######################################################################
// Utilities

// This function extracts the Cond node from the RHS of an assignment,
// if there is one and it is in a supported position, which are:
// - RHS is the Cond
// - RHS is And(Const, Cond). This And is inserted often by V3Clean.
AstNodeCond* extractCondFromRhs(AstNode* rhsp) {
    if (AstNodeCond* const condp = VN_CAST(rhsp, NodeCond)) {
        return condp;
    } else if (const AstAnd* const andp = VN_CAST(rhsp, And)) {
        if (AstNodeCond* const condp = VN_CAST(andp->rhsp(), NodeCond)) {
            if (VN_IS(andp->lhsp(), Const)) return condp;
        }
    }
    return nullptr;
}

//######################################################################
// Structure containing information required for code motion/merging

struct StmtProperties {
    AstNode* m_condp = nullptr;  // The condition expression, if a conditional node
    std::set<const AstVar*> m_rdVars;  // Variables read by this statement
    std::set<const AstVar*> m_wrVars;  // Variables writen by this statement
    bool m_isFence = false;  // Nothing should move across this statement, nor should it be merged
    AstNodeStmt* m_prevWithSameCondp = nullptr;  // Previous node in same list, with same condition
    bool writesConditionVar() const {
        // This relies on MarkVarsVisitor having been called on the condition node
        for (const AstVar* const varp : m_wrVars) {
            if (varp->user1()) return true;
        }
        return false;
    }
};

// We store the statement properties in user3 via AstUser3Allocator
using StmtPropertiesAllocator = AstUser3Allocator<AstNodeStmt, StmtProperties>;

//######################################################################
// Code motion analysis and implementation

// Pure analysis visitor that build the StmtProperties for each statement in the given
// AstNode list (following AstNode::nextp())
class CodeMotionAnalysisVisitor final : public VNVisitor {
    // NODE STATE
    // AstNodeStmt::user3   -> StmtProperties (accessed via m_stmtProperties, managed externally,
    //                         see MergeCondVisitor::process)
    // AstNode::user4       -> Used by V3Hasher
    // AstNode::user5       -> AstNode*: Set on a condition node, points to the last conditional
    //                         with that condition so far encountered in the same AstNode list

    VNUser5InUse m_user5InUse;

    StmtPropertiesAllocator& m_stmtProperties;

    // MEMBERS
    V3Hasher m_hasher;  // Used by V3DupFinder
    // Stack of a V3DupFinder used for finding identical condition expressions within one
    // statement list.
    std::vector<V3DupFinder> m_stack;
    StmtProperties* m_propsp = nullptr;  // StmtProperties structure of current AstNodeStmt

    // Extract condition expression from a megeable conditional statement, if any
    static AstNode* extractCondition(const AstNodeStmt* nodep) {
        AstNode* conditionp = nullptr;
        if (const AstNodeAssign* const assignp = VN_CAST(nodep, NodeAssign)) {
            if (AstNodeCond* const conditionalp = extractCondFromRhs(assignp->rhsp())) {
                conditionp = conditionalp->condp();
            }
        } else if (const AstNodeIf* const ifp = VN_CAST(nodep, NodeIf)) {
            conditionp = ifp->condp();
        }
        return conditionp;
    }

    void analyzeStmt(AstNodeStmt* nodep, bool tryCondMatch) {
        VL_RESTORER(m_propsp);
        // Keep hold of props of enclosing statement
        StmtProperties* const outerPropsp = m_propsp;
        // Grab the props of this statement
        m_propsp = &m_stmtProperties(nodep);

        // Extract condition from statement
        if (AstNode* const condp = extractCondition(nodep)) {
            // Remember condition node. We always need this as it is used in the later
            // traversal.
            m_propsp->m_condp = condp;
            // If this is a conditional statement, try to find an earlier one with the same
            // condition in the same list (unless we have been told not to bother because we know
            // this node is in a singleton list).
            if (tryCondMatch) {
                // Grab the duplicate finder of this list
                V3DupFinder& dupFinder = m_stack.back();
                // Find a duplicate condition
                const V3DupFinder::iterator& dit = dupFinder.findDuplicate(condp);
                if (dit == dupFinder.end()) {
                    // First time seeing this condition in the current list
                    dupFinder.insert(condp);
                    // Remember last statement with this condition (which is this statement)
                    condp->user5p(nodep);
                } else {
                    // Seen a conditional with the same condition earlier in the current list
                    AstNode* const firstp = dit->second;
                    // Add to properties for easy retrieval during optimization
                    m_propsp->m_prevWithSameCondp = static_cast<AstNodeStmt*>(firstp->user5p());
                    // Remember last statement with this condition (which is this statement)
                    firstp->user5p(nodep);
                }
            }
        }

        // Analyse this statement
        analyzeNode(nodep);

        // If there is an enclosing statement, propagate properties upwards
        if (outerPropsp) {
            // Add all rd/wr vars to outer statement
            outerPropsp->m_rdVars.insert(m_propsp->m_rdVars.cbegin(), m_propsp->m_rdVars.cend());
            outerPropsp->m_wrVars.insert(m_propsp->m_wrVars.cbegin(), m_propsp->m_wrVars.cend());
            // If this statement is impure, the enclosing statement is also impure
            if (m_propsp->m_isFence) outerPropsp->m_isFence = true;
        }
    }

    void analyzeVarRef(AstVarRef* nodep) {
        const VAccess access = nodep->access();
        AstVar* const varp = nodep->varp();
        // Gather read and written variables
        if (access.isReadOrRW()) m_propsp->m_rdVars.insert(varp);
        if (access.isWriteOrRW()) m_propsp->m_wrVars.insert(varp);
    }

    void analyzeNode(AstNode* nodep) {
        // If an impure node under a statement, mark that statement as impure
        if (m_propsp && !nodep->isPure()) m_propsp->m_isFence = true;
        // Analyze children
        iterateChildrenConst(nodep);
    }

    // VISITORS
    void visit(AstNode* nodep) override {
        // Push a new stack entry at the start of a list, but only if the list is not a
        // single element (this saves a lot of allocations in expressions)
        bool singletonListStart = false;
        if (nodep->backp()->nextp() != nodep) {  // If at head of list
            singletonListStart = nodep->nextp() == nullptr;
            if (!singletonListStart) m_stack.emplace_back(m_hasher);
        }

        // Analyse node
        if (AstNodeStmt* const stmtp = VN_CAST(nodep, NodeStmt)) {
            analyzeStmt(stmtp, /*tryCondMatch:*/ !singletonListStart);
        } else if (AstVarRef* const vrefp = VN_CAST(nodep, VarRef)) {
            analyzeVarRef(vrefp);
        } else {
            analyzeNode(nodep);
        }

        // Pop the stack at the end of a list
        if (!singletonListStart && !nodep->nextp()) m_stack.pop_back();
    }

    // CONSTRUCTOR
    CodeMotionAnalysisVisitor(AstNode* nodep, StmtPropertiesAllocator& stmtProperties)
        : m_stmtProperties(stmtProperties) {
        iterateAndNextConstNull(nodep);
    }

public:
    // Analyse the statement list starting at nodep, filling in stmtProperties.
    static void analyze(AstNode* nodep, StmtPropertiesAllocator& stmtProperties) {
        CodeMotionAnalysisVisitor{nodep, stmtProperties};
    }
};

// Predicate to check if two sets are disjoint. This is stable, as we only need
// to determine if the sets contain a shared element, which is a boolean
// property. It is also efficient as we use sorted sets, and therefore can
// enumerate elements in order (what the ordering is, is unimportant), meaning
// the worst case complexity is O(size of smaller set).
bool areDisjoint(const std::set<const AstVar*>& a, const std::set<const AstVar*>& b) {
    if (a.empty() || b.empty()) return true;
    const auto endA = a.end();
    const auto endB = b.end();
    auto itA = a.begin();
    auto itB = b.begin();
    while (true) {
        if (*itA == *itB) return false;
        if (std::less<const AstVar*>{}(*itA, *itB)) {
            itA = std::lower_bound(++itA, endA, *itB);
            if (itA == endA) return true;
        } else {
            itB = std::lower_bound(++itB, endB, *itA);
            if (itB == endB) return true;
        }
    }
}

class CodeMotionOptimizeVisitor final : public VNVisitor {
    // Do not move a node more than this many statements.
    // This bounds complexity at O(N), rather than O(N^2).
    static constexpr unsigned MAX_DISTANCE = 500;

    // NODE STATE
    // AstNodeStmt::user3   -> StmtProperties (accessed via m_stmtProperties, managed externally,
    //                         see MergeCondVisitor::process)
    // AstNodeStmt::user4   -> bool: Already processed this node

    VNUser4InUse m_user4InUse;

    const StmtPropertiesAllocator& m_stmtProperties;

    // MEMBERS

    // Predicate that checks if the order of two statements can be swapped
    bool areSwappable(const AstNodeStmt* ap, const AstNodeStmt* bp) const {
        const StmtProperties& aProps = m_stmtProperties(ap);
        const StmtProperties& bProps = m_stmtProperties(bp);
        // Don't move across fences
        if (aProps.m_isFence) return false;
        if (bProps.m_isFence) return false;
        // If either statement writes a variable that the other reads, they are not swappable
        if (!areDisjoint(aProps.m_rdVars, bProps.m_wrVars)) return false;
        if (!areDisjoint(bProps.m_rdVars, aProps.m_wrVars)) return false;
        // If they both write to the same variable, they are not swappable
        if (!areDisjoint(aProps.m_wrVars, bProps.m_wrVars)) return false;
        // Otherwise good to go
        return true;
    }

    // VISITORS
    void visit(AstNodeStmt* nodep) override {
        // Process only on first encounter
        if (nodep->user4SetOnce()) return;
        // First re-order children
        iterateChildren(nodep);
        // Grab hold of previous node with same condition
        AstNodeStmt* prevp = m_stmtProperties(nodep).m_prevWithSameCondp;
        // If no previous node with same condition, we are done
        if (!prevp) return;
#ifdef VL_DEBUG
        {  // Sanity check, only in debug build, otherwise expensive
            const AstNode* currp = prevp;
            while (currp && currp != nodep) currp = currp->nextp();
            UASSERT_OBJ(currp, nodep, "Predecessor not in same list as " << currp);
        }
#endif
        // Otherwise try to move this node backwards, as close as we can to the previous node
        // with the same condition
        if (AstNodeStmt* predp = VN_CAST(nodep->backp(), NodeStmt)) {
            // 'predp' is the newly computed predecessor node of 'nodep', which is initially
            // (without movement) the 'backp' of the node.
            for (unsigned i = MAX_DISTANCE; i; --i) {
                // If the predecessor is the previous node with the same condition, job done
                if (predp == prevp) break;
                // Don't move past a non-statement (e.g.: AstVar), or end of list
                AstNodeStmt* const backp = VN_CAST(predp->backp(), NodeStmt);
                if (!backp) break;
                // Don't swap statements if doing so would change program semantics
                if (!areSwappable(predp, nodep)) break;
                // Otherwise move 'nodep' back
                predp = backp;
            }

            // If we decided that 'nodep' should be moved back
            if (nodep->backp() != predp) {
                // Move the current node to directly follow the computed predecessor
                nodep->unlinkFrBack();
                predp->addNextHere(nodep);
                // If the predecessor is the previous node with the same condition, job done
                if (predp == prevp) return;
            }
        }
        // If we reach here, it means we were unable to move the current node all the way back
        // such that it immediately follows the previous statement with the same condition. Now
        // try to move all previous statements with the same condition forward, in the hope of
        // compacting the list further.
        for (AstNodeStmt* currp = nodep; prevp;
             currp = prevp, prevp = m_stmtProperties(currp).m_prevWithSameCondp) {
            // Move prevp (previous statement with same condition) towards currp
            if (AstNodeStmt* succp = VN_CAST(prevp->nextp(), NodeStmt)) {
                // 'succp' is the newly computed successor node of 'prevp', which is initially
                // (without movement) the 'nextp' of the node.
                for (unsigned i = MAX_DISTANCE; --i;) {
                    // If the successor of the previous statement with same condition is the
                    // target node, we are done with this predecessor
                    if (succp == currp) break;
                    // Don't move past a non-statement (e.g.: AstVar), or end of list
                    AstNodeStmt* const nextp = VN_CAST(succp->nextp(), NodeStmt);
                    if (!nextp) break;
                    // Don't swap statements if doing so would change program semantics
                    if (!areSwappable(prevp, succp)) break;
                    // Otherwise move further forward
                    succp = nextp;
                }

                // If we decided that 'prevp' should be moved forward
                if (prevp->nextp() != succp) {
                    // Move the current node to directly before the computed successor
                    prevp->unlinkFrBack();
                    succp->addHereThisAsNext(prevp);
                }
            }
        }
    }

    void visit(AstNode* nodep) override {}  // Ignore all non-statements

    // CONSTRUCTOR
    CodeMotionOptimizeVisitor(AstNode* nodep, const StmtPropertiesAllocator& stmtProperties)
        : m_stmtProperties(stmtProperties) {
        // We assert the given node is at the head of the list otherwise we might move a node
        // before the given node. This is easy to fix in the above iteration with a check on a
        // boundary node we should not move past, if we ever need to do so.
        // Note: we will do iterateAndNextNull which requires nodep->backp() != nullptr anyway
        UASSERT_OBJ(nodep->backp()->nextp() != nodep, nodep, "Must be at head of list");
        // Optimize the list
        iterateAndNextNull(nodep);
    }

public:
    // Given an AstNode list (held via AstNode::nextp()), move conditional statements as close
    // together as possible
    static AstNode* optimize(AstNode* nodep, const StmtPropertiesAllocator& stmtProperties) {
        CodeMotionOptimizeVisitor{nodep, stmtProperties};
        // It is possible for the head of the list to be moved later such that it is no longer
        // in head position. If so, rewind the list and return the new head.
        while (nodep->backp()->nextp() == nodep) nodep = nodep->backp();
        return nodep;
    }
};

//######################################################################
// Conditional merging

class MergeCondVisitor final : public VNVisitor {
private:
    // NODE STATE
    // AstVar::user1        -> bool: Set for variables referenced by m_mgCondp
    //                         (Only below MergeCondVisitor::process).
    // AstNode::user2       -> bool: Marking node as included in merge because cheap to
    //                         duplicate
    //                         (Only below MergeCondVisitor::process).
    // AstNodeStmt::user3   -> StmtProperties
    //                         (Only below MergeCondVisitor::process).
    // AstNode::user4       -> See CodeMotionAnalysisVisitor/CodeMotionOptimizeVisitor
    // AstNode::user5       -> See CodeMotionAnalysisVisitor

    // STATE
    VDouble0 m_statMerges;  // Statistic tracking
    VDouble0 m_statMergedItems;  // Statistic tracking
    VDouble0 m_statLongestList;  // Statistic tracking

    AstNode* m_mgFirstp = nullptr;  // First node in merged sequence
    AstNode* m_mgCondp = nullptr;  // The condition of the first node
    const AstNode* m_mgLastp = nullptr;  // Last node in merged sequence
    const AstNode* m_mgNextp = nullptr;  // Next node in list being examined
    uint32_t m_listLenght = 0;  // Length of current list

    std::queue<AstNode*>* m_workQueuep = nullptr;  // Node lists (via AstNode::nextp()) to merge
    // Statement properties for code motion and merging
    StmtPropertiesAllocator* m_stmtPropertiesp = nullptr;

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    // Function that processes a whole sub-tree
    void process(AstNode* nodep) {
        // Set up work queue
        std::queue<AstNode*> workQueue;
        m_workQueuep = &workQueue;
        m_workQueuep->push(nodep);

        do {
            // Set up user* for this iteration
            const VNUser1InUse user1InUse;
            const VNUser2InUse user2InUse;
            const VNUser3InUse user3InUse;
            // Statement properties only preserved for this iteration,
            // then memory is released immediately.
            StmtPropertiesAllocator stmtProperties;
            m_stmtPropertiesp = &stmtProperties;

            // Pop off current work item
            AstNode* currp = m_workQueuep->front();
            m_workQueuep->pop();

            // Analyse sub-tree list for code motion
            CodeMotionAnalysisVisitor::analyze(currp, stmtProperties);
            // Perform the code motion within the whole sub-tree list
            currp = CodeMotionOptimizeVisitor::optimize(currp, stmtProperties);

            // Merge conditionals in the whole sub-tree list (this might create new work items)
            iterateAndNextNull(currp);

            // Close pending merge, if there is one at the end of the whole sub-tree list
            if (m_mgFirstp) mergeEnd();
        } while (!m_workQueuep->empty());
    }

    // Skip past AstArraySel and AstWordSel with const index
    static AstNode* skipConstSels(AstNode* nodep) {
        while (const AstArraySel* const aselp = VN_CAST(nodep, ArraySel)) {
            // ArraySel index is not constant, so might be expensive
            if (!VN_IS(aselp->bitp(), Const)) return nodep;
            nodep = aselp->fromp();
        }
        while (const AstWordSel* const wselp = VN_CAST(nodep, WordSel)) {
            // WordSel index is not constant, so might be expensive
            if (!VN_IS(wselp->bitp(), Const)) return nodep;
            nodep = wselp->fromp();
        }
        return nodep;
    }

    // Check if this node is cheap enough that duplicating it in two branches of an
    // AstIf is not likely to cause a performance degradation.
    static bool isCheapNode(AstNode* nodep) {
        // Comments are cheap
        if (VN_IS(nodep, Comment)) return true;
        // So are some assignments
        if (const AstNodeAssign* const assignp = VN_CAST(nodep, NodeAssign)) {
            // Check LHS
            AstNode* const lhsp = skipConstSels(assignp->lhsp());
            // LHS is not a VarRef, so might be expensive
            if (!VN_IS(lhsp, VarRef)) return false;

            // Check RHS
            AstNode* const rhsp = skipConstSels(assignp->rhsp());
            // RHS is not a VarRef or Constant so might be expensive
            if (!VN_IS(rhsp, VarRef) && !VN_IS(rhsp, Const)) return false;

            // Otherwise it is a cheap assignment
            return true;
        }
        // Others are not
        return false;
    }

    // Predicate to check if an expression yields only 0 or 1 (i.e.: a 1-bit value)
    static bool yieldsOneOrZero(const AstNode* nodep) {
        UASSERT_OBJ(!nodep->isWide(), nodep, "Cannot handle wide nodes");
        if (const AstConst* const constp = VN_CAST(nodep, Const)) {
            return constp->num().toUQuad() <= 1;
        }
        if (const AstVarRef* const vrefp = VN_CAST(nodep, VarRef)) {
            const AstVar* const varp = vrefp->varp();
            return varp->widthMin() == 1 && !varp->dtypep()->isSigned();
        }
        if (const AstShiftR* const shiftp = VN_CAST(nodep, ShiftR)) {
            // Shift right by width - 1 or more
            if (const AstConst* const constp = VN_CAST(shiftp->rhsp(), Const)) {
                const AstVarRef* const vrefp = VN_CAST(shiftp->lhsp(), VarRef);
                const int width = vrefp && !vrefp->varp()->dtypep()->isSigned()
                                      ? vrefp->varp()->widthMin()
                                      : shiftp->width();
                if (constp->toSInt() >= width - 1) return true;
            }
            return false;
        }
        if (VN_IS(nodep, Eq) || VN_IS(nodep, Neq) || VN_IS(nodep, Lt) || VN_IS(nodep, Lte)
            || VN_IS(nodep, Gt) || VN_IS(nodep, Gte)) {
            return true;
        }
        if (const AstNodeBiop* const biopp = VN_CAST(nodep, NodeBiop)) {
            if (VN_IS(nodep, And))
                return yieldsOneOrZero(biopp->lhsp()) || yieldsOneOrZero(biopp->rhsp());
            if (VN_IS(nodep, Or) || VN_IS(nodep, Xor))
                return yieldsOneOrZero(biopp->lhsp()) && yieldsOneOrZero(biopp->rhsp());
            return false;
        }
        if (const AstNodeCond* const condp = VN_CAST(nodep, NodeCond)) {
            return yieldsOneOrZero(condp->expr1p()) && yieldsOneOrZero(condp->expr2p());
        }
        if (const AstCCast* const castp = VN_CAST(nodep, CCast)) {
            // Cast never sign extends
            return yieldsOneOrZero(castp->lhsp());
        }
        return false;
    }

    // Apply (1'b1 & _) cleaning mask if necessary. This is required because this pass is after
    // V3Clean, and sometimes we have an AstAnd with a 1-bit condition on one side, but a more
    // than 1-bit value on the other side, so we need to keep only the LSB.
    static AstNode* maskLsb(AstNode* nodep) {
        if (yieldsOneOrZero(nodep)) return nodep;
        // Otherwise apply masking
        AstNode* const maskp = new AstConst{nodep->fileline(), AstConst::BitTrue()};
        // Mask on left, as conventional
        return new AstAnd{nodep->fileline(), maskp, nodep};
    }

    // Fold the RHS expression of an assignment assuming the given condition state.
    // Unlink bits from the RHS which is only used once, and can be reused (is an unomdified
    // sub-tree). What remains of the RHS is expected to be deleted by the caller.
    AstNode* foldAndUnlink(AstNode* rhsp, bool condTrue) {
        if (rhsp->sameTree(m_mgCondp)) {
            return new AstConst{rhsp->fileline(), AstConst::BitTrue{}, condTrue};
        } else if (const AstNodeCond* const condp = extractCondFromRhs(rhsp)) {
            AstNode* const resp
                = condTrue ? condp->expr1p()->unlinkFrBack() : condp->expr2p()->unlinkFrBack();
            if (condp == rhsp) return resp;
            if (const AstAnd* const andp = VN_CAST(rhsp, And)) {
                UASSERT_OBJ(andp->rhsp() == condp, rhsp, "Should not try to fold this");
                return new AstAnd{andp->fileline(), andp->lhsp()->cloneTree(false), resp};
            }
        } else if (const AstAnd* const andp = VN_CAST(rhsp, And)) {
            if (andp->lhsp()->sameTree(m_mgCondp)) {
                return condTrue ? maskLsb(andp->rhsp()->unlinkFrBack())
                                : new AstConst{rhsp->fileline(), AstConst::BitFalse()};
            } else {
                UASSERT_OBJ(andp->rhsp()->sameTree(m_mgCondp), rhsp,
                            "AstAnd doesn't hold condition expression");
                return condTrue ? maskLsb(andp->lhsp()->unlinkFrBack())
                                : new AstConst{rhsp->fileline(), AstConst::BitFalse()};
            }
        } else if (VN_IS(rhsp, ArraySel) || VN_IS(rhsp, WordSel) || VN_IS(rhsp, VarRef)
                   || VN_IS(rhsp, Const)) {
            return rhsp->cloneTree(false);
        }
        // LCOV_EXCL_START
        if (debug()) rhsp->dumpTree("Don't know how to fold expression: ");
        rhsp->v3fatalSrc("Should not try to fold this during conditional merging");
        // LCOV_EXCL_STOP
    }

    void mergeEnd() {
        UASSERT(m_mgFirstp, "mergeEnd without list");
        // Drop leading cheap nodes. These were only added in the hope of finding
        // an earlier reduced form, but we failed to do so.
        while (m_mgFirstp->user2() && m_mgFirstp != m_mgLastp) {
            const AstNode* const backp = m_mgFirstp;
            m_mgFirstp = m_mgFirstp->nextp();
            --m_listLenght;
            UASSERT_OBJ(m_mgFirstp && m_mgFirstp->backp() == backp, m_mgLastp,
                        "The list should have a non-cheap element");
        }
        // Drop trailing cheap nodes. These were only added in the hope of finding
        // a later conditional to merge, but we failed to do so.
        while (m_mgLastp->user2() && m_mgFirstp != m_mgLastp) {
            const AstNode* const nextp = m_mgLastp;
            m_mgLastp = m_mgLastp->backp();
            --m_listLenght;
            UASSERT_OBJ(m_mgLastp && m_mgLastp->nextp() == nextp, m_mgFirstp,
                        "Cheap statement should not be at the front of the list");
        }
        // If the list contains a single AstNodeIf, we will want to merge its branches.
        // If so, keep hold of the AstNodeIf in this variable.
        AstNodeIf* recursivep = nullptr;
        // Merge if list is longer than one node
        if (m_mgFirstp != m_mgLastp) {
            UINFO(6, "MergeCond - First: " << m_mgFirstp << " Last: " << m_mgLastp << endl);
            ++m_statMerges;
            if (m_listLenght > m_statLongestList) m_statLongestList = m_listLenght;

            // We need a copy of the condition in the new equivalent 'if' statement,
            // and we also need to keep track of it for comparisons later.
            m_mgCondp = m_mgCondp->cloneTree(false);
            // Create equivalent 'if' statement and insert it before the first node
            AstIf* const resultp = new AstIf{m_mgCondp->fileline(), m_mgCondp};
            m_mgFirstp->addHereThisAsNext(resultp);
            // Unzip the list and insert under branches
            AstNode* nextp = m_mgFirstp;
            do {
                // Grab next pointer and unlink
                AstNode* const currp = nextp;
                nextp = currp != m_mgLastp ? currp->nextp() : nullptr;
                currp->unlinkFrBack();
                // Skip over comments
                if (VN_IS(currp, Comment)) {
                    VL_DO_DANGLING(currp->deleteTree(), currp);
                    continue;
                }
                // Count
                ++m_statMergedItems;
                if (AstNodeAssign* const assignp = VN_CAST(currp, NodeAssign)) {
                    // Unlink RHS and clone to get the 2 assignments (reusing assignp)
                    AstNode* const rhsp = assignp->rhsp()->unlinkFrBack();
                    AstNodeAssign* const thenp = assignp;
                    AstNodeAssign* const elsep = assignp->cloneTree(false);
                    // Construct the new RHSs and add to branches
                    thenp->rhsp(foldAndUnlink(rhsp, true));
                    elsep->rhsp(foldAndUnlink(rhsp, false));
                    resultp->addIfsp(thenp);
                    resultp->addElsesp(elsep);
                    // Cleanup
                    VL_DO_DANGLING(rhsp->deleteTree(), rhsp);
                } else {
                    AstNodeIf* const ifp = VN_AS(currp, NodeIf);
                    UASSERT_OBJ(ifp, currp, "Must be AstNodeIf");
                    // Move branch contents under new if
                    if (AstNode* const listp = ifp->ifsp()) {
                        resultp->addIfsp(listp->unlinkFrBackWithNext());
                    }
                    if (AstNode* const listp = ifp->elsesp()) {
                        resultp->addElsesp(listp->unlinkFrBackWithNext());
                    }
                    // Cleanup
                    VL_DO_DANGLING(ifp->deleteTree(), ifp);
                }
            } while (nextp);
            // Merge the branches of the resulting AstIf after re-analysis
            if (resultp->ifsp()) m_workQueuep->push(resultp->ifsp());
            if (resultp->elsesp()) m_workQueuep->push(resultp->elsesp());
        } else if (AstNodeIf* const ifp = VN_CAST(m_mgFirstp, NodeIf)) {
            // There was nothing to merge this AstNodeIf with, so try to merge its branches.
            // No re-analysis is required for this, so do it directly below
            recursivep = ifp;
        }
        // Reset state
        m_mgFirstp = nullptr;
        m_mgCondp = nullptr;
        m_mgLastp = nullptr;
        m_mgNextp = nullptr;
        AstNode::user1ClearTree();  // Clear marked variables
        AstNode::user2ClearTree();
        // Merge recursively within the branches of an un-merged AstNodeIF
        if (recursivep) {
            iterateAndNextNull(recursivep->ifsp());
            iterateAndNextNull(recursivep->elsesp());
            // Close a pending merge to ensure merge state is
            // reset as expected at the end of this function
            if (m_mgFirstp) mergeEnd();
        }
    }

    // Check if the node can be simplified if included under the if
    bool isSimplifiableNode(AstNode* nodep) {
        UASSERT_OBJ(m_mgFirstp, nodep, "Cannot check with empty list");
        if (const AstNodeAssign* const assignp = VN_CAST(nodep, NodeAssign)) {
            // If it's an assignment to a 1-bit signal, try reduced forms
            if (assignp->lhsp()->widthMin() == 1) {
                // Is it a 'lhs = cond & value' or 'lhs = value & cond'?
                if (const AstAnd* const andp = VN_CAST(assignp->rhsp(), And)) {
                    if (andp->lhsp()->sameTree(m_mgCondp) || andp->rhsp()->sameTree(m_mgCondp)) {
                        return true;
                    }
                }
                // Is it 'lhs = cond'?
                if (assignp->rhsp()->sameTree(m_mgCondp)) return true;
            }
        }
        return false;
    }

    bool addToList(AstNodeStmt* nodep, AstNode* condp) {
        // Set up head of new list if node is first in list
        if (!m_mgFirstp) {
            UASSERT_OBJ(condp, nodep, "Cannot start new list without condition");
            // Mark variable references in the condition
            condp->foreach<AstVarRef>([](const AstVarRef* nodep) { nodep->varp()->user1(1); });
            // Now check again if mergeable. We need this to pick up assignments to conditions,
            // e.g.: 'c = c ? a : b' at the beginning of the list, which is in fact not mergeable
            // because it updates the condition. We simply bail on these.
            if ((*m_stmtPropertiesp)(nodep).writesConditionVar()) {
                // Clear marked variables
                AstNode::user1ClearTree();
                // We did not add to the list
                return false;
            }
            m_mgFirstp = nodep;
            m_mgCondp = condp;
            m_listLenght = 0;
            // Add any preceding nodes to the list that would allow us to extend the merge
            // range
            while (true) {
                AstNodeStmt* const backp = VN_CAST(m_mgFirstp->backp(), NodeStmt);
                if (!backp || backp->nextp() != m_mgFirstp) break;  // Don't move up the tree
                const StmtProperties& props = (*m_stmtPropertiesp)(backp);
                if (props.m_isFence || props.writesConditionVar()) break;
                if (isSimplifiableNode(backp)) {
                    ++m_listLenght;
                    m_mgFirstp = backp;
                } else if (isCheapNode(backp)) {
                    backp->user2(1);
                    ++m_listLenght;
                    m_mgFirstp = backp;
                } else {
                    break;
                }
            }
        }
        // Add node
        ++m_listLenght;
        // Track end of list
        m_mgLastp = nodep;
        // Set up expected next node in list.
        m_mgNextp = nodep->nextp();
        // If last under parent, done with current list
        if (!m_mgNextp) mergeEnd();
        // We did add to the list
        return true;
    }

    // If this node is the next expected node and is helpful to add to the list, do so,
    // otherwise end the current merge. Return ture if added, false if ended merge.
    bool addIfHelpfulElseEndMerge(AstNodeStmt* nodep) {
        UASSERT_OBJ(m_mgFirstp, nodep, "List must be open");
        if (m_mgNextp == nodep) {
            if (isSimplifiableNode(nodep)) {
                if (addToList(nodep, nullptr)) return true;
            } else if (isCheapNode(nodep)) {
                nodep->user2(1);
                if (addToList(nodep, nullptr)) return true;
            }
        }
        // Not added to list, so we are done with the current list
        mergeEnd();
        return false;
    }

    bool checkOrMakeMergeable(const AstNodeStmt* nodep) {
        const StmtProperties& props = (*m_stmtPropertiesp)(nodep);
        if (props.m_isFence) return false;  // Fence node never mergeable
        // If the statement writes a condition variable of a pending merge,
        // we must end the pending merge
        if (m_mgFirstp && props.writesConditionVar()) mergeEnd();
        return true;  // Now surely mergeable
    }

    void mergeEndIfIncompatible(const AstNode* nodep, const AstNode* condp) {
        if (m_mgFirstp && (m_mgNextp != nodep || !condp->sameTree(m_mgCondp))) {
            // Node in different list, or has different condition. Finish current list.
            mergeEnd();
        }
    }

    // VISITORS
    virtual void visit(AstNodeAssign* nodep) override {
        if (AstNode* const condp = (*m_stmtPropertiesp)(nodep).m_condp) {
            // Check if mergeable
            if (!checkOrMakeMergeable(nodep)) return;
            // Close potentially incompatible pending merge
            mergeEndIfIncompatible(nodep, condp);
            // Add current node
            addToList(nodep, condp);
        } else if (m_mgFirstp) {
            addIfHelpfulElseEndMerge(nodep);
        }
    }

    virtual void visit(AstNodeIf* nodep) override {
        // Check if mergeable
        if (!checkOrMakeMergeable(nodep)) {
            // If not mergeable, try to merge the branches
            iterateAndNextNull(nodep->ifsp());
            iterateAndNextNull(nodep->elsesp());
            return;
        }
        // Close potentially incompatible pending merge
        mergeEndIfIncompatible(nodep, nodep->condp());
        // Add current node
        addToList(nodep, nodep->condp());
    }

    virtual void visit(AstNodeStmt* nodep) override {
        if (m_mgFirstp && addIfHelpfulElseEndMerge(nodep)) return;
        iterateChildren(nodep);
    }

    virtual void visit(AstCFunc* nodep) override {
        // Merge function body
        if (nodep->stmtsp()) process(nodep->stmtsp());
    }

    // For speed, only iterate what is necessary.
    virtual void visit(AstNetlist* nodep) override { iterateAndNextNull(nodep->modulesp()); }
    virtual void visit(AstNodeModule* nodep) override { iterateAndNextNull(nodep->stmtsp()); }
    virtual void visit(AstNode* nodep) override {}

public:
    // CONSTRUCTORS
    explicit MergeCondVisitor(AstNodeModule* nodep) { iterate(nodep); }
    virtual ~MergeCondVisitor() override {
        V3Stats::addStat("Optimizations, MergeCond merges", m_statMerges);
        V3Stats::addStat("Optimizations, MergeCond merged items", m_statMergedItems);
        V3Stats::addStat("Optimizations, MergeCond longest merge", m_statLongestList);
    }
};

namespace partition {
	void cleanupModule(AstNodeModule* nodep)
	{
		{ CleanUnusedVarVisitor cleaner(nodep); }
		{ CleanActiveVisitor cleaner(nodep); }
	}
	void expandAll(AstNodeModule* nodep)
	{
		{ ExpandVisitor1{nodep}; }  // Destruct before checking
	}
	void cleanAll(AstNodeModule* nodep)
	{
		{ CleanVisitor{nodep}; }  // Destruct before checking
	}

    void printCFunc(AstNetlist* nodep, const std::string& name)
    {
        { CFuncTracter{nodep, name}; }  // Destruct before checking
    }
    void mergeAll(AstNodeModule* nodep)
    {
        { MergeCondVisitor{nodep}; }
    }
}
