// (c) Copyright 2022/23 anonymous author: "VEX", Germany
// I do NOT take any responsibility or guarantee, see LICENSE.md!
// This m_code was made for EDUCATIONAL purposes ONLY!

#pragma once

#define OS_WINDOWS false
#define OS_LINUX false
#define OS_OSX false

#define CPU_AMD64 false // x86-64
#define CPU_ARM64 false // aarch64

#define COM_GCC false
#define COM_CLANG false // Also Clang-CL on Windows

#if defined(_WIN32) || defined(_WIN64)
#   undef OS_WINDOWS
#   define OS_WINDOWS true
#elif defined(__linux__)
#   undef OS_LINUX
#   define OS_LINUX true
#elif defined(__ENVIRONMENT_MAC_OS_X_VERSION_MIN_REQUIRED__)
#   undef OS_OSX
#   define OS_OSX true
#else
#   error "Unknown OS"
#endif

#if defined(__arm__)     \
 || defined(__aarch64__) \
 || defined(_M_ARM)
#   undef CPU_ARM64
#   define CPU_ARM64 true
#elif defined(_M_IX86)    \
 ||   defined(_M_X64)     \
 ||   defined(__i386__)   \
 ||   defined(__x86_64__)
#   undef CPU_AMD64
#   define CPU_AMD64 true
#else
#   error "Unknown arch"
#endif

#ifdef __GNUC__
#   undef COM_GCC
#   define COM_GCC true
#elifdef __clang__
#   undef COM_CLANG
#   define COM_CLANG true
#else
#   error "Unknown compiler"
#endif

#include <array>
#include <cassert>
#include <cstdlib>
#include <cstring>
#include <cinttypes>
#include <string_view>
#include <limits>
#include <memory>
#include <optional>
#include <iomanip>
#include <iostream>
#include <span>
#include <vector>

namespace happy_machine {
    using panic_hook = auto (*)(std::string_view msg) -> void;

    inline constinit panic_hook default_panic_hook { +[] (std::string_view msg) -> void {
        std::cerr << ":( " << msg << std::endl;
    } };

    [[noreturn]] __attribute__((cold, noinline)) inline auto panic(std::string_view msg) -> void {
        if (default_panic_hook) { (*default_panic_hook)(msg); }
        std::abort();
    }

    __attribute__((flatten)) constexpr auto verify_impl(bool cond, std::string_view msg) -> void {
        if (!cond) [[unlikely]] { panic(msg); }
    }

    #define verify(expr, msg) ::happy_machine::verify_impl((expr), (msg))

    struct page_access final {
        enum $ : std::uint8_t {
            r = 1<<0, x = 1<<1, w = 1<<2
        };
        static constexpr $ alloc   {r|w};
        static constexpr $ patch   {r|x};
        static constexpr $ dealloc {w};
    };

    using virtual_mem = std::uintptr_t;
    struct alignas(alignof(std::size_t)) valloc_header final {
        std::size_t size {};
        std::size_t align {};
        std::size_t offset {};
        page_access::$ access {};
        std::uint32_t os_access {};
        [[nodiscard]] static auto of(virtual_mem p) noexcept -> valloc_header&;
    };

    inline auto valloc_header::of(virtual_mem p) noexcept -> valloc_header& {
        return *reinterpret_cast<valloc_header*>(reinterpret_cast<std::uint8_t*>(p)-sizeof(valloc_header));
    }

    using valloc_proc = auto (*)(
        void*& out,
        std::size_t sz,
        std::size_t align,
        std::underlying_type_t<page_access::$> access,
        void* hint,
        valloc_header** out_hdr
    ) -> virtual_mem;
    using vfree_proc = auto (*)(virtual_mem p) -> void;
    using vpatch_proc = auto (*)(virtual_mem p,  std::underlying_type_t<page_access::$> access) -> void;

    [[nodiscard]] extern auto sys_valloc(
        void*& out,
        std::size_t sz,
        std::size_t align = 0,
        std::underlying_type_t<page_access::$> access = page_access::alloc,
        void* hint = nullptr,
        valloc_header** out_hdr = nullptr
    ) -> virtual_mem;
    extern auto sys_vpatch(virtual_mem p,  std::underlying_type_t<page_access::$> access) -> void;
    extern auto sys_vfree(virtual_mem p) -> void;

    inline constinit valloc_proc valloc {&sys_valloc};
    inline constinit vpatch_proc vpatch {&sys_vpatch};
    inline constinit vfree_proc vfree {&sys_vfree};
}

