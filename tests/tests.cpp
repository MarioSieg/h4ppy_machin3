#include "utest.h"
#include "../src/core.hpp"

using namespace happy_machine;

UTEST(core, sys_valloc) {
    void* o;
    valloc_header* h;
    virtual_mem mem {sys_valloc(o, sizeof(int), 0, page_access::alloc, nullptr, &h)};
    ASSERT_NE(o, nullptr);
    ASSERT_NE(h, nullptr);
    ASSERT_NE(mem, 0);
    *(int*)o = 10;
    ASSERT_EQ(*(int*)o, 10);
    ASSERT_EQ(h->size, sizeof(int) + sizeof(valloc_header));
    ASSERT_EQ(h->access, page_access::alloc);
    ASSERT_EQ(h->align, 0);
    ASSERT_EQ(h->offset, 0);
    ASSERT_NE(h->os_access, 0);
    sys_vfree(mem);
    ASSERT_EQ(mem, 0);
}

UTEST_MAIN();
