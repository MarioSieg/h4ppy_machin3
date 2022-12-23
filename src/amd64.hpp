#pragma once

#include "core.hpp"

namespace happy_machine::amd64 {
    using mscar = std::uint8_t; // machine scalar (1 byte on x86)
    constexpr auto operator ""_ma(const unsigned long long int x) -> mscar {
        return static_cast<mscar>(x);
    }

    constexpr auto max_instr_len {15_ma};

    struct ireg64 final {
        enum $ : mscar {
            rax = 0x00, rcx = 0x01, rdx = 0x02, rbx = 0x03,
            rsp = 0x04, rbp = 0x05, rsi = 0x06, rdi = 0x07,
            r8  = 0x08, r9  = 0x09, r10 = 0x0A, r11 = 0x0B,
            r12 = 0x0C, r13 = 0x0D, r14 = 0x0E, r15 = 0x0F,
            count
        };
        static_assert(count == 16);

        static constexpr std::array<std::string_view, count> names {
            "rax", "rcx", "rdx", "rbx",
            "rsp", "rbp", "rsi", "rdi",
            "r8 ", "r9 ", "r10", "r11",
            "r12", "r13", "r14", "r15",
        };

        constexpr ireg64($ x) noexcept : val {x} {}
        [[nodiscard]] constexpr auto name() const noexcept -> std::string_view  { return names[val]; }
        [[nodiscard]] constexpr auto id() const noexcept -> mscar { return val; }
        [[nodiscard]] constexpr auto is_extended() const noexcept -> bool { return val > rdi; }
        constexpr explicit operator $() const noexcept { return val; }

    private:
        $ val {};
    };

    inline auto operator <<(std::ostream& stream, ireg64 reg) -> std::ostream& {
        stream << '%' << reg.name();
        return stream;
    }

    struct ireg32 final {
        enum $ : mscar {
            eax  = ireg64::rax, ecx  = ireg64::rcx, edx  = ireg64::rdx, ebx  = ireg64::rbx,
            esp  = ireg64::rsp, ebp  = ireg64::rbp, esi  = ireg64::rsi, edi  = ireg64::rdi,
            r8d  = ireg64::r8 , r9d  = ireg64::r9 , r10d = ireg64::r10, r11d = ireg64::r11,
            r12d = ireg64::r12, r13d = ireg64::r13, r14d = ireg64::r14, r15d = ireg64::r15,
            count
        };
        static_assert(count == 16);

        static constexpr std::array<std::string_view, count> names {
            "eax", "ecx", "edx", "ebx",
            "esp", "ebp", "esi", "edi",
            "r8d", "r9d", "r10d", "r11d",
            "r12d", "r13d", "r14d", "r15d",
        };

        constexpr ireg32($ x) noexcept : val {x} {}
        [[nodiscard]] constexpr auto name() const noexcept -> std::string_view  { return names[val]; }
        [[nodiscard]] constexpr auto id() const noexcept -> mscar { return val; }
        [[nodiscard]] constexpr auto is_extended() const noexcept -> bool { return val > edi; }
        constexpr explicit operator $() const noexcept { return val; }

    private:
        $ val {};
    };

    inline auto operator <<(std::ostream& stream, ireg32 reg) -> std::ostream& {
        stream << '%' << reg.name();
        return stream;
    }

    enum struct width : mscar {
        dword = false,
        qword = true
    };

    enum struct modrm : mscar {
        reg_indirect = 0,
        signed_disp_8 = 1,
        signed_disp_32 = 2,
        reg_direct = 3
    };

    union alignas(alignof(std::uint64_t)) imm {
        std::int64_t i64 {};
        std::uint64_t u64;
        std::int32_t i32;
        std::uint32_t u32;
        float f32;
        double f64;
    };
    static_assert(sizeof(imm) == 8);

    namespace abi {
        constexpr ireg64 ra1i {OS_WINDOWS ? ireg64::rcx : ireg64::rdi};
        constexpr ireg64 ra2i {OS_WINDOWS ? ireg64::rdx : ireg64::rsi};
        constexpr ireg64 ra3i {OS_WINDOWS ? ireg64::r8 : ireg64::rdx};
        constexpr ireg64 ra4i {OS_WINDOWS ? ireg64::r9 : ireg64::rcx};
        constexpr std::uint32_t arg_reg_mask {(1zu<<ra1i.id()) | (1zu<<ra2i.id()) | (1zu<<ra3i.id()) | (1zu<<ra4i.id())};
        constexpr std::uint32_t callee_reg_mask {
            OS_WINDOWS
            ? (1zu << ireg64::rax) | (1zu << ireg64::rcx) | (1zu << ireg64::rdx) | (1zu << ireg64::r8) | (1zu << ireg64::r9) | (1zu << ireg64::r10)
            : (1zu << ireg64::rax) | (1zu << ireg64::rcx) | (1zu << ireg64::rdx) | (1zu << ireg64::rsi) | (1zu << ireg64::rdi) | (1zu << ireg64::r8) | (1zu << ireg64::r9) | (1zu << ireg64::r10)
        };
        constexpr std::uint32_t callee_saved_reg_mask {
            OS_WINDOWS
            ? (1zu << ireg64::rdi) | (1zu << ireg64::rsi) | (1zu << ireg64::rbx) | (1zu << ireg64::r12) | (1zu << ireg64::r13) | (1zu << ireg64::r14) | (1zu << ireg64::r15) | (1zu << ireg64::rbp)
            : (1zu << ireg64::rbx) | (1zu << ireg64::r12) | (1zu << ireg64::r13) | (1zu << ireg64::r14) | (1zu << ireg64::r15) | (1zu << ireg64::rbp)
        };
    }

    namespace enc {
        template <const bool Force = false>
        constexpr auto rex(mscar*& p, mscar r_mod, mscar r_idx, mscar r_rm, width wi) noexcept -> void {
            assert((r_mod & 0b1111'0000_ma) == 0);
            assert((r_idx & 0b1111'0000_ma) == 0);
            assert((r_rm  & 0b1111'0000_ma) == 0);
            constexpr auto b {0b0000'0001_ma};              /* The register in r/m field, base register in SIB byte, or reg in opcode is 8-15 rather than 0-7 */
            constexpr auto x {0b0000'0010_ma};              /* The index register in SIB byte is 8-15 rather than 0-7 */
            constexpr auto r {0b0000'0100_ma};              /* The reg field of ModRM byte is 8-15 rather than 0-7 */
            constexpr auto w {0b0000'1000_ma};              /* Operation is 64-bits instead of 32 (default) or 16 (with 0x66 prefix) */
            mscar rr {0b0100'0000_ma};
            rr |= (w & ((wi == width::qword) << 0x03_ma));
            rr |= (r & (!!(r_mod & ~0b0000'0111_ma) << 0x02_ma));
            rr |= (x & (!!(r_idx & ~0b0000'0111_ma) << 0x01_ma));
            rr |= (b & (!!(r_rm  & ~0b0000'0111_ma) << 0x00_ma));
            if (rr != 0b0100'0000_ma) [[likely]] { *p++ = rr; }
        }

        constexpr auto modrm(mscar*& p, modrm mod, mscar r, mscar m) noexcept -> void {
            *p++ = ((static_cast<std::underlying_type_t<decltype(mod)>>(mod) & 0b0000'0011_ma) << 6_ma)
                | ((r & 0b0000'0111_ma) << 3_ma)
                | (m & 0b0000'0111_ma);
        }

        constexpr auto si_opc(mscar*& p, mscar opc, mscar r, width wi) noexcept -> void {
            rex(p, 0, 0, r, wi);
            *p++ = opc | (r & 0b0000'0111_ma);
        }

        constexpr auto si_opc_modrm(mscar*& p, mscar opc, mscar r0, mscar mod, width wi) noexcept -> void {
            rex(p, 0, 0, r0, wi);
            *p++ = opc;
            modrm(p, modrm::reg_direct, mod, r0);
        }

        constexpr auto movx_ri(mscar*& p, mscar r, imm x) noexcept -> void {
            width w {x.u64 & ~((1ULL << 32) - 1) ? width::qword : width::dword};
            si_opc(p, 0b1011'1000_ma, r, w); // MOV RI
            switch (w) {
                case width::dword: *reinterpret_cast<decltype(x.u32)*>(p) = x.u32; p += sizeof x.u32; break;
                case width::qword: *reinterpret_cast<decltype(x.u64)*>(p) = x.u64; p += sizeof x.u64; break; // movabs - full 64-bit load
            }
        }

        constexpr auto alu_ri(mscar*& p, mscar opc, mscar r, imm x, width w) noexcept -> void {
            verify(!(x.u64 & ~((1ULL << 32) - 1)), "> 32-bit imm not allowed");
            if (x.i32 >= -(1 << 8) && x.i32 <= ((1 << 8) - 1)) [[likely]] {
                rex(p, 0, 0, r, w);
                *p++ = 0b1000'0011_ma;
                modrm(p, modrm::reg_direct, opc, r);
                *p++ = x.u32 & 0xFF;
            } else if (r == ireg64::rax) [[unlikely]] {
                rex(p, 0, 0, 0, w);
                *p++ = (opc << 3_ma) + 0b0000'0101_ma;
                *reinterpret_cast<decltype(x.i32)*>(p) = x.i32; p += sizeof x.i32;
            } else [[likely]] {
                rex(p, 0, 0, r, w);
                *p++ = 0b1000'0001_ma;
                modrm(p, modrm::reg_direct, opc, r);
                *reinterpret_cast<decltype(x.i32)*>(p) = x.i32; p += sizeof x.i32;
            }
        }

        constexpr auto mov_rr(mscar*& p, mscar r0, mscar r1, width wi) noexcept -> void {
            rex(p, r0, 0, r1, wi);
            *p++ = 0b1000'1011_ma; // MOV RR
            modrm(p, modrm::reg_direct, r0, r1);
        }

        constexpr auto alu_rr(mscar*& p, mscar opc, mscar r0, mscar r1, width wi) noexcept -> void {
            rex(p, r0, 0, r1, wi);
            *p++ = (opc << 3_ma) | 0b0000'0011_ma;
            modrm(p, modrm::reg_direct, r0, r1);
        }

        constexpr auto nop_chain(mscar*& vp, std::size_t n) noexcept -> void {
            auto* p{vp};
            switch (n & 15) {
                default:
                case 1 : *p++ = 0x90_ma; break;
                case 2 : *p++ = 0x40_ma; *p++ = 0x90_ma; break;
                case 3 : *p++ = 0x0F_ma; *p++ = 0x1F_ma; *p++ = 0x00_ma; break;
                case 4 : *p++ = 0x0F_ma; *p++ = 0x1F_ma; *p++ = 0x40_ma; *p++ = 0x00_ma; break;
                case 5 : *p++ = 0x0F_ma; *p++ = 0x1F_ma; *p++ = 0x44_ma; *p++ = 0x00_ma; *p++ = 0x00_ma; break;
                case 6 : *p++ = 0x66_ma; *p++ = 0x0F_ma; *p++ = 0x1F_ma; *p++ = 0x44_ma; *p++ = 0x00_ma; *p++ = 0x00_ma; break;
                case 7 : *p++ = 0x0F_ma; *p++ = 0x1F_ma; *p++ = 0x80_ma; *p++ = 0x00_ma; *p++ = 0x00_ma; *p++ = 0x00_ma; *p++ = 0x00_ma; break;
                case 8 : *p++ = 0x0F_ma; *p++ = 0x1F_ma; *p++ = 0x84_ma; *p++ = 0x00_ma; *p++ = 0x00_ma; *p++ = 0x00_ma; *p++ = 0x00_ma; *p++ = 0x00_ma; break;
                case 9 : *p++ = 0x66_ma; *p++ = 0x0F_ma; *p++ = 0x1F_ma; *p++ = 0x84_ma; *p++ = 0x00_ma; *p++ = 0x00_ma; *p++ = 0x00_ma; *p++ = 0x00_ma; *p++ = 0x00_ma; break;
                case 10: *p++ = 0x66_ma; *p++ = 0x2E_ma; *p++ = 0x0F_ma; *p++ = 0x1F_ma; *p++ = 0x84_ma; *p++ = 0x00_ma; *p++ = 0x00_ma; *p++ = 0x00_ma; *p++ = 0x00_ma; *p++ = 0x00_ma; break;
                case 11: *p++ = 0x66_ma; *p++ = 0x66_ma; *p++ = 0x2E_ma; *p++ = 0x0F_ma; *p++ = 0x1F_ma; *p++ = 0x84_ma; *p++ = 0x00_ma; *p++ = 0x00_ma; *p++ = 0x00_ma; *p++ = 0x00_ma; *p++ = 0x00_ma; break;
                case 12: *p++ = 0x66_ma; *p++ = 0x66_ma; *p++ = 0x66_ma; *p++ = 0x2E_ma; *p++ = 0x0F_ma; *p++ = 0x1F_ma; *p++ = 0x84_ma; *p++ = 0x00_ma; *p++ = 0x00_ma; *p++ = 0x00_ma; *p++ = 0x00_ma; *p++ = 0x00_ma; break;
                case 13: *p++ = 0x66_ma; *p++ = 0x66_ma; *p++ = 0x66_ma; *p++ = 0x66_ma; *p++ = 0x2E_ma; *p++ = 0x0F_ma; *p++ = 0x1F_ma; *p++ = 0x84_ma; *p++ = 0x00_ma; *p++ = 0x00_ma; *p++ = 0x00_ma; *p++ = 0x00_ma; *p++ = 0x00_ma; break;
                case 14: *p++ = 0x66_ma; *p++ = 0x66_ma; *p++ = 0x66_ma; *p++ = 0x66_ma; *p++ = 0x66_ma; *p++ = 0x2E_ma; *p++ = 0x0F_ma; *p++ = 0x1F_ma; *p++ = 0x84_ma; *p++ = 0x00_ma; *p++ = 0x00_ma; *p++ = 0x00_ma; *p++ = 0x00_ma; *p++ = 0x00_ma; break;
                case 15: *p++ = 0x66_ma; *p++ = 0x66_ma; *p++ = 0x66_ma; *p++ = 0x66_ma; *p++ = 0x66_ma; *p++ = 0x66_ma; *p++ = 0x2E_ma; *p++ = 0x0F_ma; *p++ = 0x1F_ma; *p++ = 0x84_ma; *p++ = 0x00_ma; *p++ = 0x00_ma; *p++ = 0x00_ma; *p++ = 0x00_ma; *p++ = 0x00_ma; break;
            }
            vp = p;
        }
    }

    class emitter {
    protected:
        std::vector<mscar> m_code {};

        inline auto emit_raw(mscar x) & noexcept -> void { m_code.emplace_back(x); }
        inline auto emit_raw(const mscar* begin, const mscar* end) & noexcept -> void {
            const std::ptrdiff_t diff {end - begin};
            if (diff > 0) [[likely]] {
                m_code.insert(m_code.cend(), begin, end);
            }
        }

        template <typename F> requires std::is_invocable_v<F, mscar*&>
        inline auto emit(F&& f) & noexcept -> emitter& {
            mscar buf[max_instr_len];
            std::memset(buf, 0xCC_ma, sizeof buf);
            mscar* base {buf}, *p {base};
            f(p);
            emit_raw(base, p);
            return *this;
        }

    public:
        emitter() = default;
        emitter(const emitter&) = delete;
        emitter(emitter&&) = default;
        auto operator = (const emitter&) -> emitter& = delete;
        auto operator = (emitter&&) -> emitter& = default;
        virtual ~emitter() = default;

        [[nodiscard]] inline auto machine_code() const & noexcept -> std::span<const mscar> { return m_code; }

        inline auto $mov    (ireg64 r0, imm x) & noexcept -> emitter& { return emit([=](mscar*& p) noexcept -> void { if(!x.u64) [[likely]] { set_zero(r0); return; } enc::movx_ri(p, r0.id(), x); }); }
        inline auto $nop    (std::size_t n = 1) & noexcept -> emitter& { return emit([=](mscar*& p) noexcept -> void { enc::nop_chain(p, n); });  }
        inline auto $call   (ireg64 r0) & noexcept -> emitter& { return emit([=](mscar*& p) noexcept -> void { enc::si_opc_modrm(p, 0b1111'1111_ma, r0.id(), 1_ma << 1_ma, width::dword); }); }
        inline auto $jmp    (ireg64 r0) & noexcept -> emitter& { return emit([=](mscar*& p) noexcept -> void { enc::si_opc_modrm(p, 0b1111'1111_ma, r0.id(), 1_ma << 2_ma, width::dword); }); }
        inline auto $ret    () & noexcept -> emitter& { emit_raw(0xC3_ma); return *this; }
        inline auto $int3   () & noexcept -> emitter& { emit_raw(0xCC_ma); return *this; }

        inline auto $push   (ireg64 r0) & noexcept -> emitter& { return emit([=](mscar*& p) noexcept -> void { enc::si_opc(p, 0b0101'0000_ma, r0.id(), width::dword); }); }
        inline auto $pop    (ireg64 r0) & noexcept -> emitter& { return emit([=](mscar*& p) noexcept -> void { enc::si_opc(p, 0b0101'1000_ma, r0.id(), width::dword); }); }
        inline auto $inc    (ireg64 r0) & noexcept -> emitter& { return emit([=](mscar*& p) noexcept -> void { enc::si_opc_modrm(p, 0b1111'1111_ma, r0.id(), 0b0000'0000_ma, width::qword); }); }
        inline auto $dec    (ireg64 r0) & noexcept -> emitter& { return emit([=](mscar*& p) noexcept -> void { enc::si_opc_modrm(p, 0b1111'1111_ma, r0.id(), 0b0000'0001_ma, width::qword); }); }
        inline auto $mov    (ireg64 r0, ireg64 r1) & noexcept -> emitter& { return emit([=](mscar*& p) noexcept -> void { enc::mov_rr(p, r0.id(), r1.id(), width::qword); }); }
        inline auto $add    (ireg64 r0, ireg64 r1) & noexcept -> emitter& { return emit([=](mscar*& p) noexcept -> void { enc::alu_rr(p, 0b0000'0000_ma, r0.id(), r1.id(), width::qword); }); }
        inline auto $sub    (ireg64 r0, ireg64 r1) & noexcept -> emitter& { return emit([=](mscar*& p) noexcept -> void { enc::alu_rr(p, 0b0000'0101_ma, r0.id(), r1.id(), width::qword); }); }
        inline auto $and    (ireg64 r0, ireg64 r1) & noexcept -> emitter& { return emit([=](mscar*& p) noexcept -> void { enc::alu_rr(p, 0b0000'0100_ma, r0.id(), r1.id(), width::qword); }); }
        inline auto $or     (ireg64 r0, ireg64 r1) & noexcept -> emitter& { return emit([=](mscar*& p) noexcept -> void { enc::alu_rr(p, 0b0000'0001_ma, r0.id(), r1.id(), width::qword); }); }
        inline auto $xor    (ireg64 r0, ireg64 r1) & noexcept -> emitter& { return emit([=](mscar*& p) noexcept -> void { enc::alu_rr(p, 0b0000'0110_ma, r0.id(), r1.id(), width::qword); }); }
        inline auto $cmp    (ireg64 r0, ireg64 r1) & noexcept -> emitter& { return emit([=](mscar*& p) noexcept -> void { enc::alu_rr(p, 0b0000'0111_ma, r0.id(), r1.id(), width::qword); }); }
        inline auto $add    (ireg64 r0, imm x) & noexcept -> emitter& { return emit([=](mscar*& p) noexcept -> void { if(!x.u64) [[unlikely]] { return; } enc::alu_ri(p, 0b0000'0000_ma, r0.id(), x, width::qword); }); }
        inline auto $sub    (ireg64 r0, imm x) & noexcept -> emitter& { return emit([=](mscar*& p) noexcept -> void { if(!x.u64) [[unlikely]] { return; } enc::alu_ri(p, 0b0000'0101_ma, r0.id(), x, width::qword); }); }
        inline auto $and    (ireg64 r0, imm x) & noexcept -> emitter& { return emit([=](mscar*& p) noexcept -> void { if(!x.u64) [[unlikely]] { return; } enc::alu_ri(p, 0b0000'0100_ma, r0.id(), x, width::qword); }); }
        inline auto $or     (ireg64 r0, imm x) & noexcept -> emitter& { return emit([=](mscar*& p) noexcept -> void { if(!x.u64) [[unlikely]] { return; } enc::alu_ri(p, 0b0000'0001_ma, r0.id(), x, width::qword); }); }
        inline auto $xor    (ireg64 r0, imm x) & noexcept -> emitter& { return emit([=](mscar*& p) noexcept -> void { enc::alu_ri(p, 0b0000'0110_ma, r0.id(), x, width::qword); }); }
        inline auto $cmp    (ireg64 r0, imm x) & noexcept -> emitter& { return emit([=](mscar*& p) noexcept -> void { enc::alu_ri(p, 0b0000'0111_ma, r0.id(), x, width::qword); }); }

        inline auto $push   (ireg32 r0) & noexcept -> emitter& { return emit([=](mscar*& p) noexcept -> void { enc::si_opc(p, 0b0101'0000_ma, r0.id(), width::dword); }); }
        inline auto $pop    (ireg32 r0) & noexcept -> emitter& { return emit([=](mscar*& p) noexcept -> void { enc::si_opc(p, 0b0101'1000_ma, r0.id(), width::dword); }); }
        inline auto $inc    (ireg32 r0) & noexcept -> emitter& { return emit([=](mscar*& p) noexcept -> void { enc::si_opc_modrm(p, 0b1111'1111_ma, r0.id(), 0, width::dword); }); }
        inline auto $dec    (ireg32 r0) & noexcept -> emitter& { return emit([=](mscar*& p) noexcept -> void { enc::si_opc_modrm(p, 0b1111'1111_ma, r0.id(), 1, width::dword); }); }
        inline auto $mov    (ireg32 r0, ireg32 r1) & noexcept -> emitter& { return emit([=](mscar*& p) noexcept -> void { enc::mov_rr(p, r0.id(), r1.id(), width::dword); }); }
        inline auto $add    (ireg32 r0, ireg32 r1) & noexcept -> emitter& { return emit([=](mscar*& p) noexcept -> void { enc::alu_rr(p, 0b0000'0000_ma, r0.id(), r1.id(), width::dword); }); }
        inline auto $sub    (ireg32 r0, ireg32 r1) & noexcept -> emitter& { return emit([=](mscar*& p) noexcept -> void { enc::alu_rr(p, 0b0000'0101_ma, r0.id(), r1.id(), width::dword); }); }
        inline auto $and    (ireg32 r0, ireg32 r1) & noexcept -> emitter& { return emit([=](mscar*& p) noexcept -> void { enc::alu_rr(p, 0b0000'0100_ma, r0.id(), r1.id(), width::dword); }); }
        inline auto $or     (ireg32 r0, ireg32 r1) & noexcept -> emitter& { return emit([=](mscar*& p) noexcept -> void { enc::alu_rr(p, 0b0000'0001_ma, r0.id(), r1.id(), width::dword); }); }
        inline auto $xor    (ireg32 r0, ireg32 r1) & noexcept -> emitter& { return emit([=](mscar*& p) noexcept -> void { enc::alu_rr(p, 0b0000'0110_ma, r0.id(), r1.id(), width::dword); }); }
        inline auto $cmp    (ireg32 r0, ireg32 r1) & noexcept -> emitter& { return emit([=](mscar*& p) noexcept -> void { enc::alu_rr(p, 0b0000'0111_ma, r0.id(), r1.id(), width::dword); }); }
        inline auto $add    (ireg32 r0, imm x) & noexcept -> emitter& { return emit([=](mscar*& p) noexcept -> void { if(!x.u64) [[unlikely]] { return; } enc::alu_ri(p, 0b0000'0000_ma, r0.id(), x, width::dword); }); }
        inline auto $sub    (ireg32 r0, imm x) & noexcept -> emitter& { return emit([=](mscar*& p) noexcept -> void { if(!x.u64) [[unlikely]] { return; } enc::alu_ri(p, 0b0000'0101_ma, r0.id(), x, width::dword); }); }
        inline auto $and    (ireg32 r0, imm x) & noexcept -> emitter& { return emit([=](mscar*& p) noexcept -> void { if(!x.u64) [[unlikely]] { return; } enc::alu_ri(p, 0b0000'0100_ma, r0.id(), x, width::dword); }); }
        inline auto $or     (ireg32 r0, imm x) & noexcept -> emitter& { return emit([=](mscar*& p) noexcept -> void { if(!x.u64) [[unlikely]] { return; } enc::alu_ri(p, 0b0000'0001_ma, r0.id(), x, width::dword); }); }
        inline auto $xor    (ireg32 r0, imm x) & noexcept -> emitter& { return emit([=](mscar*& p) noexcept -> void { enc::alu_ri(p, 0b0000'0110_ma, r0.id(), x, width::dword); }); }
        inline auto $cmp    (ireg32 r0, imm x) & noexcept -> emitter& { return emit([=](mscar*& p) noexcept -> void { enc::alu_ri(p, 0b0000'0111_ma, r0.id(), x, width::dword); }); }

        template <const bool BackupVolatileRegs = true>
        inline auto prologue(std::size_t frame_size = 0) & noexcept -> emitter& {
            using enum ireg64::$;
            $push(rbp);
            $mov(rbp, rsp);
            if constexpr (BackupVolatileRegs) {
                for (mscar i {}, m {1}; i < ireg64::count; ++i, m <<= 1) {
                    if ((abi::callee_saved_reg_mask & ~(1zu << rbp)) & m) {
                        $push(ireg64{static_cast<ireg64::$>(i)});
                    }
                }
            }
            if (frame_size) [[unlikely]] {
                $sub(rsp, imm {.u64=frame_size});
            }
            return *this;
        }

        template <const bool BackupVolatileRegs = true>
        inline auto epilogue(std::optional<imm> ret_val = std::nullopt) & noexcept -> emitter& {
            using enum ireg64::$;
            if constexpr (BackupVolatileRegs) {
                for (mscar i {}, m {1}; i < ireg64::count; ++i, m <<= 1) {
                    if ((abi::callee_saved_reg_mask & ~(1zu << rbp)) & m) {
                        $pop(ireg64{static_cast<ireg64::$>(i)});
                    }
                }
            }
            $mov(rsp, rbp);
            $pop(rbp);
            if (ret_val) [[unlikely]] {
                $mov(rax, *ret_val);
            }
            $ret();
            return *this;
        }

        inline auto set_zero(ireg64 r0) & noexcept -> void {
            ireg32 r {static_cast<ireg32::$>(r0.id())};
            $xor(r, r);
        }

        inline auto set_zero(ireg32 r0) & noexcept -> void { $xor(r0, r0); }

        inline auto set_zero(ireg64 from, ireg64 to) & noexcept -> void {
            verify(from.id() < to.id(), "invalid range");
            for (mscar i {from.id()}; i < to.id(); ++i) {
                set_zero(ireg64{static_cast<ireg64::$>(i)});
            }
        }

        inline auto set_zero(ireg32 from, ireg32 to) & noexcept -> void {
            verify(from.id() < to.id(), "invalid range");
            for (mscar i {from.id()}; i < to.id(); ++i) {
                set_zero(ireg64{static_cast<ireg64::$>(i)});
            }
        }

        template <typename... Regs> requires std::disjunction_v<std::is_same<std::common_type_t<Regs...>, ireg64::$>, std::is_same<std::common_type_t<Regs...>, ireg32::$>>
        inline auto set_zero(Regs&&... regs) & noexcept -> void {
            for (auto&& r : std::initializer_list<std::common_type_t<Regs...>> {regs...}) { set_zero(r); }
        }
    };

    inline auto operator << (std::ostream& stream, const emitter& emitter) -> std::ostream& {
        for (std::size_t i {}; auto&& byte : emitter.machine_code()) {
            if (i++ % 8 == 0) {
                stream << '\n';
            }
            stream << "\\x" << std::uppercase << std::setfill('0') << std::setw(2) << std::hex << static_cast<unsigned>(byte);
        }
        return stream;
    }
}
