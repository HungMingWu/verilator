#pragma once

#include "config_build.h"
#include "verilatedos.h"

class AstNetlist;

class V3ClockExtrect final {
public:
    static void extractAll(AstNetlist* nodep);
};