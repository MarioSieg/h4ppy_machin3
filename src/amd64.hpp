#pragma once

#include "core.hpp"
#include "base_emitter.hpp"

namespace happy_machine::amd64 {
    using mscar = std::uint8_t; // machine scalar (1 byte on x86)
    constexpr auto operator ""_mas(const unsigned long long int x) -> mscar {
        return static_cast<mscar>(x);
    }

    constexpr auto max_instr_len {15_mas};

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

    enum struct coco : mscar {
        eq = 0_mas, e   = 0_mas, z  = 0_mas,  ne  = 1_mas, nz  = 1_mas,
        lt = 2_mas, b   = 2_mas, c  = 2_mas,  nae = 2_mas, le  = 3_mas,
        be = 3_mas, na  = 3_mas, gt = 4_mas,  a   = 4_mas, nbe = 4_mas,
        ge = 5_mas, ae  = 5_mas, nb = 5_mas,  nc  = 5_mas, lz  = 6_mas,
        s  = 6_mas, gez = 7_mas, ns = 7_mas,  p   = 8_mas, pe  = 8_mas,
        np = 9_mas, po  = 9_mas, o  = 10_mas, no  = 11_mas,
        count
    };
    static_assert(static_cast<mscar>(coco::count) == 12_mas);

    namespace abi {
        constexpr ireg64 ra1i {OS_WINDOWS ? ireg64::rcx : ireg64::rdi};
        constexpr ireg64 ra2i {OS_WINDOWS ? ireg64::rdx : ireg64::rsi};
        constexpr ireg64 ra3i {OS_WINDOWS ? ireg64::r8 : ireg64::rdx};
        constexpr ireg64 ra4i {OS_WINDOWS ? ireg64::r9 : ireg64::rcx};
        constexpr std::uint32_t arg_reg_massk {(1zu<<ra1i.id()) | (1zu<<ra2i.id()) | (1zu<<ra3i.id()) | (1zu<<ra4i.id())};
        constexpr std::uint32_t callee_reg_massk {
            OS_WINDOWS
            ? (1zu << ireg64::rax) | (1zu << ireg64::rcx) | (1zu << ireg64::rdx) | (1zu << ireg64::r8) | (1zu << ireg64::r9) | (1zu << ireg64::r10)
            : (1zu << ireg64::rax) | (1zu << ireg64::rcx) | (1zu << ireg64::rdx) | (1zu << ireg64::rsi) | (1zu << ireg64::rdi) | (1zu << ireg64::r8) | (1zu << ireg64::r9) | (1zu << ireg64::r10)
        };
        constexpr std::uint32_t callee_saved_reg_massk {
            OS_WINDOWS
            ? (1zu << ireg64::rdi) | (1zu << ireg64::rsi) | (1zu << ireg64::rbx) | (1zu << ireg64::r12) | (1zu << ireg64::r13) | (1zu << ireg64::r14) | (1zu << ireg64::r15) | (1zu << ireg64::rbp)
            : (1zu << ireg64::rbx) | (1zu << ireg64::r12) | (1zu << ireg64::r13) | (1zu << ireg64::r14) | (1zu << ireg64::r15) | (1zu << ireg64::rbp)
        };
    }

    namespace enc {
        static constexpr std::array<mscar, static_cast<mscar>(coco::count)> cc_u_map {
            0b0111'0100_mas, /* eq  */ 0b0111'0101_mas, /* ne  */ 0b0111'0010_mas, /* lt  */ 0b0111'0110_mas, /* le  */
            0b0111'0111_mas, /* gt  */ 0b0111'0011_mas, /* ge  */ 0b0111'1000_mas, /* lz  */ 0b0111'1001_mas, /* gez */
            0b0111'1010_mas, /* p   */ 0b0111'1011_mas, /* np  */ 0b0111'0000_mas, /* o   */ 0b0111'0001_mas, /* no  */
        };

        static constexpr std::array<mscar, static_cast<mscar>(coco::count)> cc_s_map = {
            0b0111'0100_mas, /* eq  */ 0b0111'0101_mas, /* ne  */ 0b0111'1100_mas, /* lt  */ 0b0111'1110_mas, /* le  */
            0b0111'1111_mas, /* gt  */ 0b0111'1101_mas, /* ge  */ 0b0111'1000_mas, /* lz  */ 0b0111'1001_mas, /* gez */
            0b0111'1010_mas, /* p   */ 0b0111'1011_mas, /* np  */ 0b0111'0000_mas, /* o   */ 0b0111'0001_mas, /* no  */
        };

        template <const bool Force = false>
        constexpr auto rex(mscar*& p, mscar r_mod, mscar r_idx, mscar r_rm, width wi) noexcept -> void {
            enum $ : mscar {
                b = 0b0000'0001_mas,    /* The register in r/m field, base register in SIB byte, or reg in opcode is 8-15 rather than 0-7 */
                x = 0b0000'0010_mas,    /* The index register in SIB byte is 8-15 rather than 0-7 */
                r = 0b0000'0100_mas,    /* The reg field of ModRM byte is 8-15 rather than 0-7 */
                w = 0b0000'1000_mas     /* Operation is 64-bits instead of 32 (default) or 16 (with 0x66 prefix) */
            };
            assert((r_mod & 0b1111'0000_mas) == 0);
            assert((r_idx & 0b1111'0000_mas) == 0);
            assert((r_rm  & 0b1111'0000_mas) == 0);
            mscar rr {0b0100'0000_mas};
            rr |= (w & ((wi == width::qword) << 0x03_mas));
            rr |= (r & (!!(r_mod & ~0b0000'0111_mas) << 0x02_mas));
            rr |= (x & (!!(r_idx & ~0b0000'0111_mas) << 0x01_mas));
            rr |= (b & (!!(r_rm  & ~0b0000'0111_mas) << 0x00_mas));
            if (rr != 0b0100'0000_mas) [[likely]] { *p++ = rr; }
        }

        constexpr auto modrm(mscar*& p, modrm mod, mscar r, mscar m) noexcept -> void {
            *p++ = ((static_cast<std::underlying_type_t<decltype(mod)>>(mod) & 0b0000'0011_mas) << 6_mas)
                | ((r & 0b0000'0111_mas) << 3_mas)
                | (m & 0b0000'0111_mas);
        }

        constexpr auto si_opc(mscar*& p, mscar opc, mscar r, width wi) noexcept -> void {
            rex(p, 0, 0, r, wi);
            *p++ = opc | (r & 0b0000'0111_mas);
        }

        constexpr auto si_opc_modrm(mscar*& p, mscar opc, mscar r0, mscar mod, width wi) noexcept -> void {
            rex(p, 0, 0, r0, wi);
            *p++ = opc;
            modrm(p, modrm::reg_direct, mod, r0);
        }

        inline auto movx_ri(mscar*& p, mscar r, imm x) noexcept -> void {
            width w {x.is_immx<std::uint32_t>() ? width::dword : width::qword};
            si_opc(p, 0b1011'1000_mas, r, w); // MOV RI
            switch (w) {
                case width::dword: *reinterpret_cast<decltype(x.u32)*>(p) = x.u32; p += sizeof x.u32; break;
                case width::qword: *reinterpret_cast<decltype(x.u64)*>(p) = x.u64; p += sizeof x.u64; break; // movabs - full 64-bit load
            }
        }

        inline auto alu_ri(mscar*& p, mscar opc, mscar r, imm x, width w) noexcept -> void {
            verify(x.is_immx<std::int32_t>(), "> 32-bit imm not allowed");
            if (x.is_immx<std::int8_t>()) [[likely]] {
                rex(p, 0, 0, r, w);
                *p++ = 0b1000'0011_mas;
                modrm(p, modrm::reg_direct, opc, r);
                *p++ = x.u32 & 0xFF;
            } else if (r == ireg64::rax) [[unlikely]] {
                rex(p, 0, 0, 0, w);
                *p++ = (opc << 3_mas) + 0b0000'0101_mas;
                *reinterpret_cast<decltype(x.i32)*>(p) = x.i32; p += sizeof x.i32;
            } else [[likely]] {
                rex(p, 0, 0, r, w);
                *p++ = 0b1000'0001_mas;
                modrm(p, modrm::reg_direct, opc, r);
                *reinterpret_cast<decltype(x.i32)*>(p) = x.i32; p += sizeof x.i32;
            }
        }

        constexpr auto mov_rr(mscar*& p, mscar r0, mscar r1, width wi) noexcept -> void {
            rex(p, r0, 0, r1, wi);
            *p++ = 0b1000'1011_mas; // MOV RR
            modrm(p, modrm::reg_direct, r0, r1);
        }

        constexpr auto alu_rr(mscar*& p, mscar opc, mscar r0, mscar r1, width wi) noexcept -> void {
            rex(p, r0, 0, r1, wi);
            *p++ = (opc << 3_mas) | 0b0000'0011_mas;
            modrm(p, modrm::reg_direct, r0, r1);
        }

        inline auto br8(mscar*& p, coco cc, std::int8_t x, bool is_signed) noexcept -> void {
            *p++ = is_signed ? cc_s_map[static_cast<mscar>(cc)] : cc_u_map[static_cast<mscar>(cc)];
            *p++ = *reinterpret_cast<mscar*>(x);
        }

        inline auto br32(mscar*& p, coco cc, std::int32_t x, bool is_signed) noexcept -> void {
            *p++ = 0x0F_mas;
            *p++ = is_signed ? cc_s_map[static_cast<mscar>(cc)] + 0x10_mas : cc_u_map[static_cast<mscar>(cc)] + 0x10_mas;
            *reinterpret_cast<decltype(x)*>(p) = x; p += sizeof x;
        }

        inline auto branch(mscar*& p, coco cc, imm target, bool is_signed, width wi) noexcept -> void {
            rex(p, 0, 0, 0, wi);
            auto offs {static_cast<std::int32_t>(reinterpret_cast<mscar*>(target.u64) - p - 2)};
            if (imm{offs}.is_immx<std::int8_t>()) [[likely]] { br8(p, cc, static_cast<std::int8_t>(offs), is_signed); }
            else {
                offs = static_cast<std::int32_t>(reinterpret_cast<mscar*>(target.u64) - p - 6);
                br32(p, cc, offs, is_signed);
            }
        }

        constexpr auto nop_chain(mscar*& vp, std::size_t n) noexcept -> void {
            auto* p {vp};
            switch (n & 0x0F) {
                default:
                case 0x01: *p++ = 0x90_mas; break;
                case 0x02: *p++ = 0x40_mas; *p++ = 0x90_mas; break;
                case 0x03: *p++ = 0x0F_mas; *p++ = 0x1F_mas; *p++ = 0x00_mas; break;
                case 0x04: *p++ = 0x0F_mas; *p++ = 0x1F_mas; *p++ = 0x40_mas; *p++ = 0x00_mas; break;
                case 0x05: *p++ = 0x0F_mas; *p++ = 0x1F_mas; *p++ = 0x44_mas; *p++ = 0x00_mas; *p++ = 0x00_mas; break;
                case 0x06: *p++ = 0x66_mas; *p++ = 0x0F_mas; *p++ = 0x1F_mas; *p++ = 0x44_mas; *p++ = 0x00_mas; *p++ = 0x00_mas; break;
                case 0x07: *p++ = 0x0F_mas; *p++ = 0x1F_mas; *p++ = 0x80_mas; *p++ = 0x00_mas; *p++ = 0x00_mas; *p++ = 0x00_mas; *p++ = 0x00_mas; break;
                case 0x08: *p++ = 0x0F_mas; *p++ = 0x1F_mas; *p++ = 0x84_mas; *p++ = 0x00_mas; *p++ = 0x00_mas; *p++ = 0x00_mas; *p++ = 0x00_mas; *p++ = 0x00_mas; break;
                case 0x09: *p++ = 0x66_mas; *p++ = 0x0F_mas; *p++ = 0x1F_mas; *p++ = 0x84_mas; *p++ = 0x00_mas; *p++ = 0x00_mas; *p++ = 0x00_mas; *p++ = 0x00_mas; *p++ = 0x00_mas; break;
                case 0x0A: *p++ = 0x66_mas; *p++ = 0x2E_mas; *p++ = 0x0F_mas; *p++ = 0x1F_mas; *p++ = 0x84_mas; *p++ = 0x00_mas; *p++ = 0x00_mas; *p++ = 0x00_mas; *p++ = 0x00_mas; *p++ = 0x00_mas; break;
                case 0x0B: *p++ = 0x66_mas; *p++ = 0x66_mas; *p++ = 0x2E_mas; *p++ = 0x0F_mas; *p++ = 0x1F_mas; *p++ = 0x84_mas; *p++ = 0x00_mas; *p++ = 0x00_mas; *p++ = 0x00_mas; *p++ = 0x00_mas; *p++ = 0x00_mas; break;
                case 0x0C: *p++ = 0x66_mas; *p++ = 0x66_mas; *p++ = 0x66_mas; *p++ = 0x2E_mas; *p++ = 0x0F_mas; *p++ = 0x1F_mas; *p++ = 0x84_mas; *p++ = 0x00_mas; *p++ = 0x00_mas; *p++ = 0x00_mas; *p++ = 0x00_mas; *p++ = 0x00_mas; break;
                case 0x0D: *p++ = 0x66_mas; *p++ = 0x66_mas; *p++ = 0x66_mas; *p++ = 0x66_mas; *p++ = 0x2E_mas; *p++ = 0x0F_mas; *p++ = 0x1F_mas; *p++ = 0x84_mas; *p++ = 0x00_mas; *p++ = 0x00_mas; *p++ = 0x00_mas; *p++ = 0x00_mas; *p++ = 0x00_mas; break;
                case 0x0E: *p++ = 0x66_mas; *p++ = 0x66_mas; *p++ = 0x66_mas; *p++ = 0x66_mas; *p++ = 0x66_mas; *p++ = 0x2E_mas; *p++ = 0x0F_mas; *p++ = 0x1F_mas; *p++ = 0x84_mas; *p++ = 0x00_mas; *p++ = 0x00_mas; *p++ = 0x00_mas; *p++ = 0x00_mas; *p++ = 0x00_mas; break;
                case 0x0F: *p++ = 0x66_mas; *p++ = 0x66_mas; *p++ = 0x66_mas; *p++ = 0x66_mas; *p++ = 0x66_mas; *p++ = 0x66_mas; *p++ = 0x2E_mas; *p++ = 0x0F_mas; *p++ = 0x1F_mas; *p++ = 0x84_mas; *p++ = 0x00_mas; *p++ = 0x00_mas; *p++ = 0x00_mas; *p++ = 0x00_mas; *p++ = 0x00_mas; break;
            }
            vp = p;
        }
    }

    class emitter : public base_emitter<mscar, ireg32, ireg64> {
    protected:
        inline auto emit_raw(mscar x) & noexcept -> void { m_code.emplace_back(x); }
        inline auto emit_raw(const mscar* begin, const mscar* end) & noexcept -> void {
            const std::ptrdiff_t diff {end - begin};
            if (diff) [[likely]] {
                m_code.insert(m_code.cend(), begin, end);
            }
        }

        template <typename F> requires std::is_invocable_v<F, mscar*&>
        inline auto emit(F&& f) & noexcept -> emitter& {
            mscar buf[max_instr_len];
            std::memset(buf, 0xCC_mas, sizeof buf);
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

        inline auto $mov    (ireg64 r0, imm x) & noexcept -> emitter& { return emit([=](mscar*& p) noexcept -> void { if(!x.u64) [[likely]] { set_zero(r0); return; } enc::movx_ri(p, r0.id(), x); }); }
        inline auto $nop    (std::size_t n = 1) & noexcept -> emitter& { return emit([=](mscar*& p) noexcept -> void { enc::nop_chain(p, n); });  }
        inline auto $call   (ireg64 r0) & noexcept -> emitter& { return emit([=](mscar*& p) noexcept -> void { enc::si_opc_modrm(p, 0b1111'1111_mas, r0.id(), 1_mas << 1_mas, width::dword); }); }
        inline auto $jmp    (ireg64 r0) & noexcept -> emitter& { return emit([=](mscar*& p) noexcept -> void { enc::si_opc_modrm(p, 0b1111'1111_mas, r0.id(), 1_mas << 2_mas, width::dword); }); }
        inline auto $ret    () & noexcept -> emitter& { emit_raw(0xC3_mas); return *this; }
        inline auto $int3   () & noexcept -> emitter& { emit_raw(0xCC_mas); return *this; }
        inline auto $jmp    (coco cc, imm target) noexcept -> emitter& { return emit([=](mscar*& p) noexcept -> void { enc::branch(p, cc, target, true, width::dword); }); }

        inline auto $push   (ireg64 r0) & noexcept -> emitter& { return emit([=](mscar*& p) noexcept -> void { enc::si_opc(p, 0b0101'0000_mas, r0.id(), width::dword); }); }
        inline auto $pop    (ireg64 r0) & noexcept -> emitter& { return emit([=](mscar*& p) noexcept -> void { enc::si_opc(p, 0b0101'1000_mas, r0.id(), width::dword); }); }
        inline auto $inc    (ireg64 r0) & noexcept -> emitter& { return emit([=](mscar*& p) noexcept -> void { enc::si_opc_modrm(p, 0b1111'1111_mas, r0.id(), 0b0000'0000_mas, width::qword); }); }
        inline auto $dec    (ireg64 r0) & noexcept -> emitter& { return emit([=](mscar*& p) noexcept -> void { enc::si_opc_modrm(p, 0b1111'1111_mas, r0.id(), 0b0000'0001_mas, width::qword); }); }
        inline auto $mov    (ireg64 r0, ireg64 r1) & noexcept -> emitter& { return emit([=](mscar*& p) noexcept -> void { enc::mov_rr(p, r0.id(), r1.id(), width::qword); }); }
        inline auto $add    (ireg64 r0, ireg64 r1) & noexcept -> emitter& { return emit([=](mscar*& p) noexcept -> void { enc::alu_rr(p, 0b0000'0000_mas, r0.id(), r1.id(), width::qword); }); }
        inline auto $sub    (ireg64 r0, ireg64 r1) & noexcept -> emitter& { return emit([=](mscar*& p) noexcept -> void { enc::alu_rr(p, 0b0000'0101_mas, r0.id(), r1.id(), width::qword); }); }
        inline auto $and    (ireg64 r0, ireg64 r1) & noexcept -> emitter& { return emit([=](mscar*& p) noexcept -> void { enc::alu_rr(p, 0b0000'0100_mas, r0.id(), r1.id(), width::qword); }); }
        inline auto $or     (ireg64 r0, ireg64 r1) & noexcept -> emitter& { return emit([=](mscar*& p) noexcept -> void { enc::alu_rr(p, 0b0000'0001_mas, r0.id(), r1.id(), width::qword); }); }
        inline auto $xor    (ireg64 r0, ireg64 r1) & noexcept -> emitter& { return emit([=](mscar*& p) noexcept -> void { enc::alu_rr(p, 0b0000'0110_mas, r0.id(), r1.id(), width::qword); }); }
        inline auto $cmp    (ireg64 r0, ireg64 r1) & noexcept -> emitter& { return emit([=](mscar*& p) noexcept -> void { enc::alu_rr(p, 0b0000'0111_mas, r0.id(), r1.id(), width::qword); }); }
        inline auto $add    (ireg64 r0, imm x) & noexcept -> emitter& { return emit([=](mscar*& p) noexcept -> void { if(!x.u64) [[unlikely]] { return; } enc::alu_ri(p, 0b0000'0000_mas, r0.id(), x, width::qword); }); }
        inline auto $sub    (ireg64 r0, imm x) & noexcept -> emitter& { return emit([=](mscar*& p) noexcept -> void { if(!x.u64) [[unlikely]] { return; } enc::alu_ri(p, 0b0000'0101_mas, r0.id(), x, width::qword); }); }
        inline auto $and    (ireg64 r0, imm x) & noexcept -> emitter& { return emit([=](mscar*& p) noexcept -> void { if(!x.u64) [[unlikely]] { return; } enc::alu_ri(p, 0b0000'0100_mas, r0.id(), x, width::qword); }); }
        inline auto $or     (ireg64 r0, imm x) & noexcept -> emitter& { return emit([=](mscar*& p) noexcept -> void { if(!x.u64) [[unlikely]] { return; } enc::alu_ri(p, 0b0000'0001_mas, r0.id(), x, width::qword); }); }
        inline auto $xor    (ireg64 r0, imm x) & noexcept -> emitter& { return emit([=](mscar*& p) noexcept -> void { enc::alu_ri(p, 0b0000'0110_mas, r0.id(), x, width::qword); }); }
        inline auto $cmp    (ireg64 r0, imm x) & noexcept -> emitter& { return emit([=](mscar*& p) noexcept -> void { enc::alu_ri(p, 0b0000'0111_mas, r0.id(), x, width::qword); }); }

        inline auto $push   (ireg32 r0) & noexcept -> emitter& { return emit([=](mscar*& p) noexcept -> void { enc::si_opc(p, 0b0101'0000_mas, r0.id(), width::dword); }); }
        inline auto $pop    (ireg32 r0) & noexcept -> emitter& { return emit([=](mscar*& p) noexcept -> void { enc::si_opc(p, 0b0101'1000_mas, r0.id(), width::dword); }); }
        inline auto $inc    (ireg32 r0) & noexcept -> emitter& { return emit([=](mscar*& p) noexcept -> void { enc::si_opc_modrm(p, 0b1111'1111_mas, r0.id(), 0, width::dword); }); }
        inline auto $dec    (ireg32 r0) & noexcept -> emitter& { return emit([=](mscar*& p) noexcept -> void { enc::si_opc_modrm(p, 0b1111'1111_mas, r0.id(), 1, width::dword); }); }
        inline auto $mov    (ireg32 r0, ireg32 r1) & noexcept -> emitter& { return emit([=](mscar*& p) noexcept -> void { enc::mov_rr(p, r0.id(), r1.id(), width::dword); }); }
        inline auto $add    (ireg32 r0, ireg32 r1) & noexcept -> emitter& { return emit([=](mscar*& p) noexcept -> void { enc::alu_rr(p, 0b0000'0000_mas, r0.id(), r1.id(), width::dword); }); }
        inline auto $sub    (ireg32 r0, ireg32 r1) & noexcept -> emitter& { return emit([=](mscar*& p) noexcept -> void { enc::alu_rr(p, 0b0000'0101_mas, r0.id(), r1.id(), width::dword); }); }
        inline auto $and    (ireg32 r0, ireg32 r1) & noexcept -> emitter& { return emit([=](mscar*& p) noexcept -> void { enc::alu_rr(p, 0b0000'0100_mas, r0.id(), r1.id(), width::dword); }); }
        inline auto $or     (ireg32 r0, ireg32 r1) & noexcept -> emitter& { return emit([=](mscar*& p) noexcept -> void { enc::alu_rr(p, 0b0000'0001_mas, r0.id(), r1.id(), width::dword); }); }
        inline auto $xor    (ireg32 r0, ireg32 r1) & noexcept -> emitter& { return emit([=](mscar*& p) noexcept -> void { enc::alu_rr(p, 0b0000'0110_mas, r0.id(), r1.id(), width::dword); }); }
        inline auto $cmp    (ireg32 r0, ireg32 r1) & noexcept -> emitter& { return emit([=](mscar*& p) noexcept -> void { enc::alu_rr(p, 0b0000'0111_mas, r0.id(), r1.id(), width::dword); }); }
        inline auto $add    (ireg32 r0, imm x) & noexcept -> emitter& { return emit([=](mscar*& p) noexcept -> void { if(!x.u64) [[unlikely]] { return; } enc::alu_ri(p, 0b0000'0000_mas, r0.id(), x, width::dword); }); }
        inline auto $sub    (ireg32 r0, imm x) & noexcept -> emitter& { return emit([=](mscar*& p) noexcept -> void { if(!x.u64) [[unlikely]] { return; } enc::alu_ri(p, 0b0000'0101_mas, r0.id(), x, width::dword); }); }
        inline auto $and    (ireg32 r0, imm x) & noexcept -> emitter& { return emit([=](mscar*& p) noexcept -> void { if(!x.u64) [[unlikely]] { return; } enc::alu_ri(p, 0b0000'0100_mas, r0.id(), x, width::dword); }); }
        inline auto $or     (ireg32 r0, imm x) & noexcept -> emitter& { return emit([=](mscar*& p) noexcept -> void { if(!x.u64) [[unlikely]] { return; } enc::alu_ri(p, 0b0000'0001_mas, r0.id(), x, width::dword); }); }
        inline auto $xor    (ireg32 r0, imm x) & noexcept -> emitter& { return emit([=](mscar*& p) noexcept -> void { enc::alu_ri(p, 0b0000'0110_mas, r0.id(), x, width::dword); }); }
        inline auto $cmp    (ireg32 r0, imm x) & noexcept -> emitter& { return emit([=](mscar*& p) noexcept -> void { enc::alu_ri(p, 0b0000'0111_mas, r0.id(), x, width::dword); }); }

        inline virtual auto prologue(std::size_t frame_size, bool backup_volatile_regs) & noexcept -> void final override {
            using enum ireg64::$;
            $push(rbp);
            $mov(rbp, rsp);
            if (backup_volatile_regs) {
                for (mscar i {}, m {1}; i < ireg64::count; ++i, m <<= 1) {
                    if ((abi::callee_saved_reg_massk & ~(1zu << rbp)) & m) {
                        $push(ireg64{static_cast<ireg64::$>(i)});
                    }
                }
            }
            if (frame_size) [[unlikely]] {
                $sub(rsp, imm {.u64=frame_size});
            }
        }

        inline virtual auto epilogue(std::optional<imm> ret_val, bool backup_volatile_regs) & noexcept -> void final override {
            using enum ireg64::$;
            if (backup_volatile_regs) {
                for (mscar i {}, m {1}; i < ireg64::count; ++i, m <<= 1) {
                    if ((abi::callee_saved_reg_massk & ~(1zu << rbp)) & m) {
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
        }

        inline virtual auto set_zero(ireg64 r0) & noexcept -> void final override {
            ireg32 r {static_cast<ireg32::$>(r0.id())};
            $xor(r, r);
        }

        inline virtual auto set_zero(ireg32 r0) & noexcept -> void final override {
            $xor(r0, r0);
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
