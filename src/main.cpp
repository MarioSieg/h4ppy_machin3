#include <iostream>

#include "amd64.hpp"

using namespace happy_machine;
using namespace amd64;

auto main() -> signed {
    using enum ireg64::$;
    emitter e {};
    e.prologue(32);
    e.$int3();
    e.epilogue();
    std::cout << e;
    return 0;
}
