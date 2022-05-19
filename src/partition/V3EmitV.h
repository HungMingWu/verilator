#pragma once
#include "config_build.h"
#include "verilatedos.h"

class AstNode;

namespace partition
{
	void verilogForTree(const AstNode* nodep, std::ostream& os = std::cout);
}
