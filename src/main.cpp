#include <iostream>

#include "amd64.hpp"

using namespace happy_machine;
using namespace amd64;

auto main() -> signed {
    using enum ireg64::$;
    emitter e {};
    e.prologue(32);
    e.$int3();
    e.$inc(rax);
    e.$dec(ireg32::esp);
    e.$inc(r11);
    e.$call(rax);
    e.$jmp(rax);
    e.$cmp(rax, r10);
    e.$cmp(rax, imm{22});
    e.epilogue();
    std::cout << e;
    return 0;
}
