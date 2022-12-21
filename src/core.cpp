// (c) Copyright 2022/23 anonymous author: "VEX", Germany
// I do NOT take any responsibility or guarantee, see LICENSE.md!
// This m_code was made for EDUCATIONAL purposes ONLY!

#include "core.hpp"

#include <bit>

#if OS_LINUX
#   include <unistd.h>
#   include <sys/mman.h>
#endif

namespace happy_machine {

#if OS_LINUX
    [[nodiscard]] static constexpr auto map_protection(std::underlying_type_t<page_access::$> access) noexcept -> int {
        int ret{};
        using enum page_access::$;
        if (access & r) ret |= PROT_READ;
        if (access & w) ret |= PROT_WRITE;
        if (access & x) ret |= PROT_EXEC;
        return ret;
    }
#endif

    auto sys_valloc(
        void*& out,
        std::size_t sz,
        std::size_t align,
        std::underlying_type_t<page_access::$> access,
        void *hint,
        valloc_header **out_hdr
    ) -> virtual_mem {
        const std::size_t off{align-1+sizeof(void*)};
        sz += align ? off : 0;
        void* base;
        std::uint32_t os_access;
        #if OS_LINUX
        {
            int prot {map_protection(access)};
            int err {errno};
            void* p {::mmap(hint, sz, prot, MAP_PRIVATE|MAP_ANONYMOUS, -1, 0)};
            errno = err;
            verify(p, "mmap failed");
            base = p;
            os_access = std::bit_cast<decltype(os_access)>(prot);
        }
        #else
        #   error "sys_valloc not implemented"
        #endif
        auto& h {valloc_header::of(reinterpret_cast<virtual_mem>(base))};
        h.size = sz;
        h.align = align;
        h.offset = off;
        h.access = static_cast<page_access::$>(access);
        h.os_access = os_access;
        if (out) { *out_hdr = &h; }
        if (align) {
            void** aligned {reinterpret_cast<void**>((reinterpret_cast<std::uintptr_t>(base) + off) & ~(align - 1))};
            *(aligned-1) = base;
            out = aligned;
        } else { out = base; }
        return reinterpret_cast<virtual_mem>(base);
    }

    auto sys_vpatch(virtual_mem p, std::underlying_type_t<page_access::$> access) -> void {
        if (!p) [[unlikely]] { return; }
    }

    auto sys_vfree(virtual_mem p) -> void {
        if (!p) [[unlikely]] { return; }
        sys_vpatch(p, page_access::dealloc);
        #if OS_LINUX
            auto& h { valloc_header::of(p) };
            verify(!::munmap(reinterpret_cast<void*>(p), h.size), "munmap failed");
        #else
        #   error "sys_vfree not implemented"
        #endif
    }
}
