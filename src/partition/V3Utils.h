#pragma once
#include "V3Ast.h"
namespace partition 
{
    struct CollectPort final : public VNVisitor {
        std::vector<AstVar*> m_vars;
        void visit(AstVar* nodep) override {
            if (nodep->isIO()) m_vars.push_back(nodep);
        }
        void visit(AstNode* nodep) override { iterateChildrenConst(nodep); };
        CollectPort(AstNodeModule* nodep) { iterate(nodep); }
        ~CollectPort() = default;
    };
    void cleanupModule(AstNodeModule* nodep);
}
