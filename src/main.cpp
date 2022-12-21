#include <iostream>

#include "amd64.hpp"

using namespace happy_machine;
using namespace amd64;

auto main() -> signed {
    amd64::emitter e {};
    e.prologue(32);
    e.$int3();
    {
        using enum amd64::ireg64::$;
        e.$add(rax, imm{10});
        e.$add(rax, imm{1<<16});
        e.$add(r15, imm{0xBABA});
        e.$add(r15, imm{2});
        e.$mov(r8, imm{0});
    }

    {
        using enum amd64::ireg32::$;
        e.$add(eax, imm{10});
        e.$add(eax, imm{1<<16});
        e.$add(r15d, imm{0xBABA});
        e.$add(r15d, imm{2});
    }

    e.epilogue();
    std::cout << e;
    return 0;
}
