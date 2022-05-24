#include "V3EmitCBase.h"
#include "V3Utils.h"

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
namespace partition
{
	void cleanupModule(AstNodeModule* nodep)
	{
		{ CleanUnusedVarVisitor cleaner(nodep); }
		{ CleanActiveVisitor cleaner(nodep); }
	}
}