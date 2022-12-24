#pragma once

#include <cstdint>
#include <concepts>
#include <type_traits>
#include <limits>

namespace happy_machine {
    union alignas(alignof(std::uint64_t)) imm {
        std::int64_t i64 {};
        std::uint64_t u64;
        std::int32_t i32;
        std::uint32_t u32;
        float f32;
        double f64;

        template <typename T> requires std::is_integral_v<T>
        [[nodiscard]] constexpr auto is_immx() const noexcept -> bool {
            if constexpr (std::is_signed_v<T>) {
                return i64 >= std::numeric_limits<T>::min() && i64 <= std::numeric_limits<T>::max();
            } else {
                return u64 <= std::numeric_limits<T>::max();
            }
        }
    };
    static_assert(sizeof(imm) == 8);

    struct label final {
        std::size_t offset {};
    };

    template <typename MScar, typename Reg32, typename Reg64>
    concept emitter_signature = requires {
        requires std::is_integral_v<MScar>;
        requires sizeof(MScar) < sizeof(std::int64_t);
        requires std::is_trivially_copyable_v<Reg32>;
        requires std::is_trivially_copyable_v<Reg64>;
        requires std::is_constructible_v<Reg32, typename Reg32::$>;
        requires std::is_constructible_v<Reg64, typename Reg64::$>;
    };

    template <typename MScar, typename Reg32, typename Reg64> requires emitter_signature<MScar, Reg32, Reg64>
    class base_emitter {
    protected:
        std::vector<MScar> m_code {};

        base_emitter() = default;

    public:
        using MScarT = MScar;
        using Reg32T = Reg32;
        using Reg64T = Reg64;

        base_emitter(const  base_emitter&) = delete;
        base_emitter(base_emitter&&) noexcept = default;
        auto operator = (const base_emitter&) -> base_emitter& = delete;
        auto operator = (base_emitter&&) noexcept -> base_emitter& = default;
        virtual ~base_emitter() = default;

        [[nodiscard]] inline auto machine_code() const & noexcept -> std::span<const MScar> { return m_code; }

        virtual auto prologue(std::size_t frame_size, bool backup_volatile_regs) & noexcept -> void = 0;
        virtual auto epilogue(std::optional<imm> ret_val, bool backup_volatile_regs) & noexcept -> void = 0;
        virtual auto set_zero(Reg32 r0) & noexcept -> void = 0;
        virtual auto set_zero(Reg64 r0) & noexcept -> void = 0;
        inline auto set_zero_range(Reg32 from, Reg32 to) & noexcept -> void {
            verify(from.id() < to.id(), "invalid range");
            for (auto i {from.id()}; i < to.id(); ++i) {
                set_zero(Reg32{static_cast<typename Reg32::$>(i)});
            }
        }
        inline auto set_zero_range(Reg64 from, Reg64 to) & noexcept -> void {
            verify(from.id() < to.id(), "invalid range");
            for (auto i {from.id()}; i < to.id(); ++i) {
                set_zero(Reg64{static_cast<typename Reg64::$>(i)});
            }
        }
        template <typename... Regs> requires
            std::disjunction_v<std::is_same<std::common_type_t<Regs...>, typename Reg32::$>,
            std::is_same<std::common_type_t<Regs...>, typename Reg64::$>>
        inline auto set_zero(Regs&&... regs) & noexcept -> void {
            for (auto&& r : std::initializer_list<std::common_type_t<Regs...>> {regs...}) { set_zero(r); }
        }

        // create label with name
        [[nodiscard]] inline virtual auto operator [](std::string_view name) const noexcept -> label {
            return label {.offset = m_code.size()};
        }
    };
}
