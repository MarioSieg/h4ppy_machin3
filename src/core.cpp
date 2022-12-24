// (c) Copyright 2022/23 anonymous author: "VEX", Germany
// I do NOT take any responsibility or guarantee, see LICENSE.md!
// This m_code was made for EDUCATIONAL purposes ONLY!

#include "core.hpp"

#include <bit>

#if OS_LINUX
#   include <unistd.h>
#   include <sys/mman.h>
#elif OS_WINDOWS
#   define WIN32_LEAN_AND_MEAN
#   include <windows.h>
#endif

namespace happy_machine {

#if OS_LINUX
    [[nodiscard]] static constexpr auto map_protection(std::underlying_type_t<page_access::$> access) noexcept -> int {
        int ret {};
        using enum page_access::$;
        if (access & r) ret |= PROT_READ;
        if (access & w) ret |= PROT_WRITE;
        if (access & x) ret |= PROT_EXEC;
        return ret;
    }
#elif OS_WINDOWS
    [[nodiscard]] static constexpr auto map_protection(std::underlying_type_t<page_access::$> access) noexcept -> DWORD {
        int ret {};
        using enum page_access::$;
        switch (access) {
            case r: return PAGE_READONLY;
            case r | w: return PAGE_READWRITE;
            case r | w | x: return PAGE_EXECUTE_READWRITE;
            case r | x: return PAGE_EXECUTE_READ;
            default: verify(false, "invalid page access flags");
        }
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
        const std::size_t off{align - 1 + sizeof(void*)};
        sz += align ? off + sizeof(valloc_header) : sizeof(valloc_header);
        void* base;
        std::uint32_t os_access;
        #if OS_LINUX
        {
            const int prot {map_protection(access)};
            int err {errno};
            void* p {::mmap(hint, sz, prot, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0)};
            errno = err;
            verify(p, "mmap failed");
            base = p;
            os_access = std::bit_cast<decltype(os_access)>(prot);
        }
        #elif OS_WINDOWS
        {
            const DWORD prot {map_protection(access)};
            DWORD err {::GetLastError()};
            void* p {::VirtualAlloc(hint, sz, MEM_RESERVE | MEM_COMMIT | MEM_TOP_DOWN, prot)};
            ::SetLastError(err);
            verify(p, "virtual alloc failed");
            base = p;
            os_access = std::bit_cast<decltype(os_access)>(prot);
        }
        #else
        #   error "Missing OS impl"
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
        #elif OS_WINDOWS
            verify(::VirtualFree(reinterpret_cast<void*>(p), 0, MEM_RELEASE), "virtual free failed");
        #else
        #   error "Missing OS impl"
        #endif
    }
}
