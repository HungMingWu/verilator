#pragma once
#include "config_build.h"
#include "verilatedos.h"

class AstNode;

namespace partition
{
	void verilogForTree(const AstNode* nodep, const std::string& new_module_name = "", std::ostream& os = std::cout);
}
