#pragma once

//#include <algorithm>	// C++20 constexpr algorithms are not yet supported
#include <array>
//#include <bit>		// We don't have C++20 <bit> yet
#include <cassert>
#include <cstddef>		// std::uint32_t, etc.
#include <cstring>		// std::memcpy; not needed if C++20 std::bit_cast is used instead
#include <iterator>		// std::make_reverse_iterator; not needed if C++20 constexpr algorithms are used instead
#include <limits>		// std::numeric_limits
#include <utility>		// std::index_sequence & friends
#include <type_traits>	// std::integral_constant

#if defined(_MSC_VER)
#include <intrin.h>
#endif

struct grisu_impl_common {
	// The result of this function is valid for
	// exp in [-65536,+65536], but may not be valid outside.
	static constexpr int log10_pow2(int e) {
		// The next 32 digits are 0x7de7fbcc
		constexpr std::uint32_t log10_2_up_to_32 = 0x4d104d42;

		return int(
			// Calculate 0x0.4d104d42 * exp * 2^32
			(std::int64_t(e) * log10_2_up_to_32
				// Perform ceiling
				+ ((std::int64_t(1) << 32) - 1))
			// Perform arithmetic-shift
			>> 32);
	}

	static constexpr std::size_t log2p1(std::uint64_t x) noexcept {
		// C++20 std::log2p1 is not yet supported
		//return std::log2p1(x);

		std::size_t ret = 0;
		auto inspect = [&](unsigned int shft) {
			if ((x >> shft) != 0) {
				x >>= shft;
				ret += shft;
			}
		};

		inspect(32);
		inspect(16);
		inspect(8);
		inspect(4);
		inspect(2);
		inspect(1);

		return ret + x;
	}

	// Represent numbers as "significand * 2^exponent"
	template <class Float>
	struct fp_t {
		static_assert(std::numeric_limits<Float>::is_iec559&&
			std::numeric_limits<Float>::radix == 2 &&
			(sizeof(Float) == 4 || sizeof(Float) == 8),
			"Grisu algorithm only applies to IEEE754 binary32 and binary64 formats!");

		using significand_type = std::conditional_t<
			sizeof(Float) == 4,
			std::uint32_t,
			std::uint64_t>;

		static constexpr std::size_t significand_bits =
			sizeof(significand_type) * std::numeric_limits<unsigned char>::digits;

		using half_significand_type = std::conditional_t<
			sizeof(Float) == 4,
			std::uint16_t,
			std::uint32_t>;

		static constexpr std::size_t half_significand_bits =
			sizeof(half_significand_type) * std::numeric_limits<unsigned char>::digits;

		// exponent should lie inside [min_exponent, max_exponent]
		static constexpr int min_exponent =
			std::numeric_limits<Float>::min_exponent - std::numeric_limits<Float>::digits
			- int(significand_bits) + 1;
		static constexpr int max_exponent =
			std::numeric_limits<Float>::max_exponent - int(significand_bits);
		static_assert(min_exponent < 0 && max_exponent > 0 && -min_exponent >= max_exponent);

		significand_type	significand;
		int					exponent;
	};

	template <class Float>
	struct signed_fp_t : fp_t<Float> {
		bool				is_negative;
	};

	// A simple bignum class for cached powers-of-10 computation
	template <std::size_t max_bits>
	class bignum_holder {
		using element_type = std::uint64_t;

		static constexpr std::size_t element_number_of_bits =
			sizeof(element_type) * std::numeric_limits<unsigned char>::digits;
		static constexpr std::size_t array_size =
			(max_bits + element_number_of_bits - 1) / element_number_of_bits;

		std::array<element_type, array_size> elements_;

		struct leading_one_pos_t {
			std::size_t		element_pos;
			std::size_t		bit_pos;		// 1 ~ element_number_of_bits
		} leading_one_pos_;

		/* Boilerplates for constexpr initialization */
		template <std::size_t I>
		static constexpr element_type zero_initialize_element() {
			return 0;
		}
		template <std::size_t... I>
		static constexpr std::array<element_type, array_size>
			zero_initialize_array(std::index_sequence<I...>)
		{
			return{ zero_initialize_element<I>()... };
		}

		template <std::size_t... I>
		constexpr bignum_holder(std::index_sequence<I...>, element_type x) :
			elements_{ zero_initialize_element<I>()... },
			leading_one_pos_{ 0, log2p1(x) }
		{
			assert(x != 0);
			elements_[0] = x;
		}

	public:
		bignum_holder() = default;

		constexpr bignum_holder(element_type x) :
			bignum_holder(std::make_index_sequence<array_size>{}, x) {}

		constexpr element_type operator[](std::size_t idx) const {
			assert(idx < array_size);
			return elements_[idx];
		}

		// Repeat multiplying 2 until the number becomes bigger than or equal to the given number
		// Returns the number of multiplications
		// Precondition: n should be bigger than or equal to the current number
		constexpr std::size_t multiply_2_until(bignum_holder const& n) & {
			std::size_t number_of_multiplications = 0;

			// Perform left-shift to match the leading-1 position
			// Perform element-wise shift first
			assert(leading_one_pos_.element_pos <= n.leading_one_pos_.element_pos);
			auto element_pos_offset = n.leading_one_pos_.element_pos - leading_one_pos_.element_pos;
			if (element_pos_offset > 0) {
				number_of_multiplications = element_pos_offset * element_number_of_bits;

				// C++20 constexpr algorithms are not supported yet
				//std::move_backward(elements_.begin(),
				//	elements_.begin() + leading_one_pos_.element_pos + 1,
				//	elements_.begin() + n.leading_one_pos_.element_pos + 1);
				auto d_itr = elements_.begin() + n.leading_one_pos_.element_pos;
				for (auto itr = std::make_reverse_iterator(elements_.begin() + leading_one_pos_.element_pos + 1);
					itr != std::make_reverse_iterator(elements_.begin());
					++itr)
				{
					*d_itr = *itr;
					--d_itr;
				}

				// C++20 constexpr algorithms are not supported yet
				//std::fill_n(elements_.begin(), element_pos_offset, 0);
				for (std::size_t idx = 0; idx < element_pos_offset; ++idx)
					elements_[idx] = 0;

				leading_one_pos_.element_pos += element_pos_offset;
			}
			// And then perform bit-wise shift
			auto bit_pos_offset = std::ptrdiff_t(n.leading_one_pos_.bit_pos) -
				std::ptrdiff_t(leading_one_pos_.bit_pos);
			number_of_multiplications += bit_pos_offset;
			if (bit_pos_offset > 0) {
				// Left-shfit
				auto shft = std::size_t(bit_pos_offset);
				auto remaining_bits = element_number_of_bits - shft;
				for (auto idx = leading_one_pos_.element_pos; idx > 0; --idx) {
					auto bits_to_transfer = elements_[idx - 1] >> remaining_bits;

					elements_[idx] <<= shft;
					elements_[idx] |= bits_to_transfer;
				}
				elements_[0] <<= shft;
			}
			else if (bit_pos_offset < 0) {
				// Right-shift
				auto shft = std::size_t(-bit_pos_offset);
				auto remaining_bits = element_number_of_bits - shft;
				elements_[0] >>= shft;
				for (std::size_t idx = 1; idx <= leading_one_pos_.element_pos; ++idx) {
					auto bits_to_transfer = elements_[idx] << remaining_bits;

					elements_[idx - 1] |= bits_to_transfer;
					elements_[idx] >>= shft;
				}
			}
			leading_one_pos_.bit_pos = n.leading_one_pos_.bit_pos;

			// Compare the shifted number with the given number
			bool is_bigger_than_or_equal_to = true;
			for (auto idx = std::ptrdiff_t(leading_one_pos_.element_pos); idx >= 0; --idx) {
				if (elements_[idx] > n[idx])
					break;
				else if (elements_[idx] < n[idx]) {
					is_bigger_than_or_equal_to = false;
					break;
				}
			}

			// If our number is still less
			if (!is_bigger_than_or_equal_to) {
				// Shift one more bit
				++number_of_multiplications;
				if (leading_one_pos_.bit_pos == element_number_of_bits) {
					leading_one_pos_.bit_pos = 1;
					++leading_one_pos_.element_pos;
					assert(leading_one_pos_.element_pos != array_size);
				}
				else
					++leading_one_pos_.bit_pos;

				constexpr auto remaining_bits = element_number_of_bits - 1;
				for (auto idx = leading_one_pos_.element_pos; idx > 0; --idx) {
					auto bits_to_transfer = elements_[idx - 1] >> remaining_bits;

					elements_[idx] <<= 1;
					elements_[idx] |= bits_to_transfer;
				}
				elements_[0] <<= 1;
			}

			return number_of_multiplications;
		}

		// Multiply 5 to the current number
		constexpr void multiply_5() & {
			auto times_4 = zero_initialize_array(std::make_index_sequence<array_size>{});
			leading_one_pos_t times_4_leading_one_pos{
				leading_one_pos_.element_pos,
				leading_one_pos_.bit_pos + 2
			};

			// Fix leading-1 position
			auto shift_start_pos = leading_one_pos_.element_pos;
			if (times_4_leading_one_pos.bit_pos > element_number_of_bits) {
				assert(leading_one_pos_.element_pos + 1 != array_size);

				times_4_leading_one_pos.bit_pos -= element_number_of_bits;
				++times_4_leading_one_pos.element_pos;

				++shift_start_pos;
			}

			// Calculate copied and times_4
			for (auto idx = shift_start_pos; idx > 0; --idx) {
				auto bits_to_transfer = elements_[idx - 1] >> (element_number_of_bits - 2);

				times_4[idx] = elements_[idx] << 2;
				times_4[idx] |= bits_to_transfer;
			}
			times_4[0] = elements_[0] << 2;

			// Add
			elements_[0] += times_4[0];
			unsigned int carry = (elements_[0] < times_4[0]) ? 1 : 0;

			for (std::size_t idx = 1; idx <= times_4_leading_one_pos.element_pos; ++idx) {
				auto copied_with_carry = elements_[idx] + carry;
				unsigned int first_carry = (copied_with_carry < elements_[idx]) ? 1 : 0;

				elements_[idx] = copied_with_carry + times_4[idx];
				carry = first_carry | ((elements_[idx] < times_4[idx]) ? 1 : 0);
			}

			if (carry != 0) {
				leading_one_pos_.element_pos = times_4_leading_one_pos.element_pos + 1;
				leading_one_pos_.bit_pos = 1;

				elements_[leading_one_pos_.element_pos] = 1;
			}
			else {
				leading_one_pos_.element_pos = times_4_leading_one_pos.element_pos;

				// The expression "element_type(1) << times_4_leading_one_pos.bit_pos"
				// is UB if times_4_leading_one_pos.bit_pos == element_number_of_bits,
				// so we have to use the following instead:
				auto threshold = element_type(-1) >>
					(element_number_of_bits - times_4_leading_one_pos.bit_pos);
				if (elements_[leading_one_pos_.element_pos] > threshold)
					leading_one_pos_.bit_pos = times_4_leading_one_pos.bit_pos + 1;
				else
					leading_one_pos_.bit_pos = times_4_leading_one_pos.bit_pos;
			}

			assert(leading_one_pos_.element_pos != array_size);
			assert(leading_one_pos_.bit_pos <= element_number_of_bits);
		}

		// Subtract another number
		// Precondition: n should be strictly smaller than or equal to the current number
		constexpr bignum_holder& operator-=(bignum_holder const& n) & {
			unsigned int carry = elements_[0] < n[0] ? 1 : 0;
			elements_[0] -= n[0];

			std::size_t idx = 1;
			for (; idx <= n.leading_one_pos_.element_pos; ++idx) {
				auto n_with_carry = n[idx] + carry;
				unsigned int first_carry = (n_with_carry < n[idx]) ? 1 : 0;

				carry = first_carry | ((elements_[idx] < n_with_carry) ? 1 : 0);
				elements_[idx] -= n_with_carry;
			}

			if (carry != 0) {
				while (elements_[idx] == 0) {
					elements_[idx++] = element_type(-1);
					assert(idx < array_size);
				}
				--elements_[idx];
			}

			// Find the new leading-1 position
			for (idx = leading_one_pos_.element_pos; idx > 0; --idx) {
				if (elements_[idx] != 0)
					break;
			}
			assert(elements_[idx] != 0);

			leading_one_pos_.element_pos = idx;
			leading_one_pos_.bit_pos = log2p1(elements_[idx]);

			return *this;
		}

		template <class Float>
		constexpr fp_t<Float> get_fp() const noexcept {
			using significand_type = typename fp_t<Float>::significand_type;
			constexpr auto target_bits = fp_t<Float>::significand_bits;
			static_assert(target_bits <= element_number_of_bits, "Access size is too large");

			fp_t<Float> ret{ significand_type(
				(elements_[leading_one_pos_.element_pos] << (element_number_of_bits - leading_one_pos_.bit_pos))
				>> (element_number_of_bits - target_bits)),
				int(leading_one_pos_.bit_pos - target_bits
					+ element_number_of_bits * leading_one_pos_.element_pos) };

			if (leading_one_pos_.element_pos != 0 && leading_one_pos_.bit_pos < target_bits) {
				auto remaining_bits = target_bits - leading_one_pos_.bit_pos;
				auto bits_to_transfer = elements_[leading_one_pos_.element_pos - 1]
					>> (element_number_of_bits - remaining_bits);

				ret.significand |= bits_to_transfer;
			}

			// Perform rounding; perform increment iff the next bit is set
			auto increment_ret = [&]() {
				if (++ret.significand == 0) {
					ret.significand = significand_type(1) << (target_bits - 1);
					++ret.exponent;
				}
			};
			if (leading_one_pos_.bit_pos > target_bits) {
				auto mask = element_type(1) << (leading_one_pos_.bit_pos - target_bits - 1);
				if ((mask & elements_[leading_one_pos_.element_pos]) != 0)
					increment_ret();
			}
			else if (leading_one_pos_.element_pos != 0) {
				auto mask = element_type(1) <<
					(element_number_of_bits - (target_bits - leading_one_pos_.bit_pos) - 1);
				if ((mask & elements_[leading_one_pos_.element_pos - 1]) != 0)
					increment_ret();
			}

			return ret;
		}
	};
};

template <class Float>
struct grisu_impl : public grisu_impl_common {
	using fp_t = grisu_impl_common::fp_t<Float>;
	using significand_type = typename fp_t::significand_type;
	using half_significand_type = typename fp_t::half_significand_type;
	using signed_fp_t = grisu_impl_common::signed_fp_t<Float>;

private:
	static constexpr auto significand_size = std::size_t(std::numeric_limits<Float>::digits - 1);
	static constexpr auto exponent_size = fp_t::significand_bits - 1 - significand_size;
	static constexpr auto exponent_bias = int((1 << exponent_size) - std::numeric_limits<Float>::max_exponent - 1);

	static constexpr significand_type sign_mask = significand_type(1) << (fp_t::significand_bits - 1);

	static constexpr auto fp_t_normal_exponent = exponent_bias + int(fp_t::significand_bits) - 1;
	static constexpr auto fp_t_subnormal_exponent = std::numeric_limits<Float>::min_exponent - int(significand_size) - 1;

	// NOTE: significand is NOT extracted
	static signed_fp_t decompose_float_impl(Float x) {
		assert(std::isfinite(x));

		signed_fp_t ret;

		// C++20 std::bit_cast is not yet supported
		// ret.significand = std::bit_cast<significand_type>(x);
		static_assert(sizeof(significand_type) == sizeof(Float) &&
			alignof(significand_type) == alignof(Float));
		std::memcpy(&ret.significand, &x, sizeof(Float));

		ret.exponent = int((~sign_mask & ret.significand) >> significand_size);
		ret.is_negative = (sign_mask & ret.significand) != 0;

		return ret;
	}

public:
	// This function is not directly related to the Grisu2 algorithm
	static signed_fp_t get_normalized_fp_t(Float x) {
		signed_fp_t ret = decompose_float_impl(x);

		// Normal
		if (ret.exponent != 0) {
			ret.significand <<= exponent_size;
			ret.significand |= sign_mask;
			ret.exponent -= fp_t_normal_exponent;
		}
		// Subnormal or zero
		else {
			ret.significand &= (~sign_mask);
			auto shift_amount = fp_t::significand_bits - log2p1(ret.significand);
			ret.significand <<= shift_amount;
			ret.exponent = int(fp_t_subnormal_exponent - shift_amount);
		}

		assert(ret.significand == 0 ||
			(ret.exponent >= fp_t::min_exponent && ret.exponent <= fp_t::max_exponent));

		return ret;
	}

	static signed_fp_t grisu2(Float x)
	{
		/* Compute boundaries */

		auto mp = decompose_float_impl(x);
		significand_type mm_significand;

		// Normal
		if (mp.exponent != 0) {
			constexpr auto unit = significand_type(1) << (fp_t::significand_bits - significand_size - 1);
			constexpr auto half_unit = unit >> 1;

			mp.significand <<= exponent_size;
			// If the significand part of x was zero, then mp.significand & ~sign_mask should be zero.
			// If this is the case and also mp.exponent is not 1,
			// then the distance from the left boundary is shorter than usual.
			auto edge_case_correction = half_unit >>
				int((mp.significand & (~sign_mask)) == 0 && mp.exponent != 1);
			mp.significand |= (sign_mask | half_unit);
			mm_significand = mp.significand - unit;
			mm_significand |= edge_case_correction;
			mp.exponent -= fp_t_normal_exponent;
		}
		// Subnormal or zero
		else {
			mp.significand &= (~sign_mask);

			// Subnormal
			if (mp.significand != 0) {
				mp.significand <<= 1;

				mm_significand = mp.significand - 1;
				++mp.significand;

				auto shift_amount = fp_t::significand_bits - log2p1(mp.significand);
				mp.significand <<= shift_amount;
				mm_significand <<= shift_amount;
				mp.exponent = int(fp_t_subnormal_exponent - shift_amount - 1);
			}
			// Zero
			else
				return mp;
		}


		/* Compute M_\downarrow^+ and M_\uparrow^- and \delta */

		auto mk = log10_pow2(alpha - mp.exponent - 1);
		assert(k_min <= mk && mk <= k_max);
		{
			if constexpr (sizeof(Float) == 8) {
#if defined(_MSC_VER) && defined(_M_AMD64)
				std::uint64_t high;
				auto low = _umul128(mp.significand, powers_of_10[mk - k_min].significand, &high);
				mp.significand = high + (low >> 63);

				low = _umul128(mm_significand, powers_of_10[mk - k_min].significand, &high);
				mm_significand = high + (low >> 63);
#elif (__GNUC__ > 4 || (__GNUC__ == 4 && __GNUC_MINOR__ >= 6)) && defined(__x86_64__)
				auto p = (unsigned __int128)(mp.significand) *
					(unsigned __int128)(powers_of_10[mk - k_min].significand);
				auto low = std::uint64_t(p);
				mp.significand = std::uint64_t(p >> 64) + (low >> 63);

				p = (unsigned __int128)(mm_significand) *
					(unsigned __int128)(powers_of_10[mk - k_min].significand);
				low = std::uint64_t(p);
				mm_significand = std::uint64_t(p >> 64) + (low >> 63);
#else
				constexpr significand_type mask =
					(significand_type(1) << fp_t::half_significand_bits) - significand_type(1);

				auto ap = mp.significand >> fp_t::half_significand_bits;
				auto bp = mp.significand & mask;
				auto am = mm_significand >> fp_t::half_significand_bits;
				auto bm = mm_significand & mask;
				auto c = powers_of_10[mk - k_min].significand >> fp_t::half_significand_bits;
				auto d = powers_of_10[mk - k_min].significand & mask;

				auto apc = ap * c;
				auto bpc = bp * c;
				auto amc = am * c;
				auto bmc = bm * c;

				auto apd = ap * d;
				auto bpd = bp * d;
				auto amd = am * d;
				auto bmd = bm * d;

				auto intermediate_p = (bpd >> fp_t::half_significand_bits)
					+ (apd & mask) + (bpc & mask)
					+ (significand_type(1) << (fp_t::half_significand_bits - 1));
				auto intermediate_m = (bmd >> fp_t::half_significand_bits)
					+ (amd & mask) + (bmc & mask)
					+ (significand_type(1) << (fp_t::half_significand_bits - 1));

				mp.significand = apc + (intermediate_p >> fp_t::half_significand_bits)
					+ (apd >> fp_t::half_significand_bits) + (bpc >> fp_t::half_significand_bits);
				mm_significand = amc + (intermediate_m >> fp_t::half_significand_bits)
					+ (amd >> fp_t::half_significand_bits) + (bmc >> fp_t::half_significand_bits);
#endif
			}
			else {
				static_assert(sizeof(Float) == 4);
				auto p = (std::uint64_t)(mp.significand) *
					(std::uint64_t)(powers_of_10[mk - k_min].significand);
				auto low = std::uint32_t(p);
				mp.significand = std::uint32_t(p >> 32) + (low >> 31);

				p = (std::uint64_t)(mm_significand) *
					(std::uint64_t)(powers_of_10[mk - k_min].significand);
				low = std::uint32_t(p);
				mm_significand = std::uint32_t(p >> 32) + (low >> 31);
			}

			mp.exponent += powers_of_10[mk - k_min].exponent + fp_t::significand_bits;
			assert(mp.exponent >= alpha && mp.exponent <= gamma);
		}
		// Note that neither overflow nor underflow can occur here:
		--mp.significand;
		++mm_significand;
		assert(mp.significand > mm_significand);
		auto delta_significand = mp.significand - mm_significand;


		/* Find kappa and P */

		// In Grisu2 algorithm, it can be shown that
		// \delta >= 3 * 2^(e_{w^+} + e_c + q) * (2^{q-p-3} - 1)
		//        >= 3 * 2^\alpha * (2^{q-p-3} - 1).
		// Thus,
		//   - for binary32 (aka "float" type), \delta >= 189 * 2^\alpha, and
		//   - for binary64 (aka "double" type), \delta >= 1533 * 2^\alpha.
		// Hence, for our choice of \alpha (alpha = 0), \delta is always strictly larger than 100.
		// This implies that kappa is at least 2, and for binary64, kappa is at least 3.
		// Because of the fact that mp.exponent is at most gamma = 3, assuming kappa >= 3 simplifies
		// a lot of remaining operations; therefore, we start our computation with kappa = 3.
		// For binary32 case, this requires us to do some additional things for
		// handling the case kappa == 2.

		// divisor = 5^mp.exponent * 10^(kappa - mp.exponent)
		auto divisor = significand_type(1000) >> mp.exponent;

		// Find q, r satisfying mp.significand = divisor * q + r, or equivalently,
		// 2^mp.exponent * mp.significand = 1000 * q + (2^mp.exponent * r).
		// The following is an optimization of this computation completely avoiding integer division;
		// remember that modern compilers are able to optimize out division-by-constant
		// with a multiplication together with a shift, or a series of those.
		auto q0 = mp.significand / significand_type(125);
		auto r0 = mp.significand % significand_type(125);

		mp.significand = q0 >> (gamma - mp.exponent);
		auto r = significand_type(125) * (q0 ^ (mp.significand << (gamma - mp.exponent))) + r0;

		mp.exponent = 3 - mk;

		// We should check if kappa == 2 for binary32
		if constexpr (sizeof(Float) == 4) {
			if (r > delta_significand) {
				// Compute s satisfying 2^mp.exponent * mp.significand = 100 * s + t
				mp.significand *= significand_type(10);
				mp.significand += r / significand_type(100);
				--mp.exponent;

				return mp;
			}
		}
		assert(r <= delta_significand);
		delta_significand -= r;

		// Perform binary search to find kappa
		// At this point, mp.significand <= std::numeric_limits<significand_type>::max() / 125, so
		//   - for binary32 (aka "float" type), mp.significand is of at most 8 decimal digits,
		//   - for binary64 (aka "double" type), mp.significand is of at most 18 decimal digits.
		significand_type q;
		auto perform_search = [&](auto power_of_ten, auto exponent) {
			q = mp.significand / decltype(power_of_ten)::value;
			r = divisor * (mp.significand % decltype(power_of_ten)::value);

			if (r <= delta_significand) {
				mp.significand = q;
				mp.exponent += decltype(exponent)::value;
				delta_significand -= r;
				divisor *= decltype(power_of_ten)::value;

				return false;
			}
			return true;
		};
		if constexpr (sizeof(Float) == 8) {
			if (perform_search(std::integral_constant<significand_type, 1'00000000'00000000>{},
				std::integral_constant<int, 16>{}))
			{
				perform_search(std::integral_constant<significand_type, 100000000>{},
					std::integral_constant<int, 8>{});
				perform_search(std::integral_constant<significand_type, 10000>{},
					std::integral_constant<int, 4>{});
				perform_search(std::integral_constant<significand_type, 100>{},
					std::integral_constant<int, 2>{});
			}
			perform_search(std::integral_constant<significand_type, 10>{},
				std::integral_constant<int, 1>{});
		}
		else {
			static_assert(sizeof(Float) == 4);
			perform_search(std::integral_constant<significand_type, 10000>{},
				std::integral_constant<int, 4>{});
			perform_search(std::integral_constant<significand_type, 100>{},
				std::integral_constant<int, 2>{});
			perform_search(std::integral_constant<significand_type, 10>{},
				std::integral_constant<int, 1>{});
		}

		return mp;
	}

private:
	static constexpr int alpha = 0;
	static constexpr int gamma = 3;
	static constexpr int k_min = log10_pow2(alpha - fp_t::max_exponent - 1);
	static constexpr int k_max = log10_pow2(alpha - fp_t::min_exponent - 1);
	static_assert(k_min < 0 && k_max > 0 && k_max >= -k_min);

	static constexpr std::size_t cache_size = k_max - k_min + 1;

	static constexpr std::size_t cache_max_bits = alpha - fp_t::min_exponent;

	// Merely to make compute_powers_of_10() constexpr
	template <std::size_t I>
	static constexpr fp_t zero_initialize_fp_t() noexcept {
		return{ 0, 0 };
	}
	template <std::size_t... I>
	static constexpr std::array<fp_t, cache_size> zero_initialize_cache(
		std::index_sequence<I...>) noexcept
	{
		return{ zero_initialize_fp_t<I>()... };
	}

public:
	static constexpr std::array<fp_t, cache_size> compute_powers_of_10()
	{
		std::array<fp_t, cache_size> ret = zero_initialize_cache(
			std::make_index_sequence<cache_size>{});

		auto cache = [&ret](int k) -> fp_t & {
			return ret[k - k_min];
		};

		bignum_holder<cache_max_bits> power_of_5 = 1;

		cache(0) = power_of_5.template get_fp<Float>();

		int k = 1;
		for (; k <= -k_min; ++k) {
			power_of_5.multiply_5();

			// Compute positive power
			// - Compute 5^k; the remaining 2^k then increments the exponent by k
			cache(k) = power_of_5.template get_fp<Float>();
			cache(k).exponent += k;

			// Compute negative power
			// - Again, we can factor out 2^-k part by decrementing the exponent by k
			// - To compute 1/5^k, set d = 1 and repeat the following procedure:
			//   - Find the minimum n >= 0 such that d * 2^n >= 5^k; this means that d/5^k >= 1/2^n,
			//     thus the nth digit of the binary expansion of d/5^k is 1
			//   - Set d = d * 2^n - 5^k; this effectively calculates d/5^k - 1/2^n
			//   - Now we conclude that the next (n-1) digits of the binary expansion of 1/5^k are zero,
			//     while the next digit is one
			//   - Repeat until reaching the maximum precision
			bignum_holder<cache_max_bits> dividend = 1;
			cache(-k).significand = 1;
			cache(-k).exponent = -k - int(dividend.multiply_2_until(power_of_5) + fp_t::significand_bits - 1);

			std::size_t accumulated_exp = 0;
			while (true) {
				dividend -= power_of_5;
				auto new_exp = dividend.multiply_2_until(power_of_5);

				accumulated_exp += new_exp;
				if (accumulated_exp >= fp_t::significand_bits) {
					cache(-k).significand <<= (fp_t::significand_bits - 1 - (accumulated_exp - new_exp));

					// Perform rounding; perform increment iff the next bit is set
					if (accumulated_exp == fp_t::significand_bits) {
						// Add one
						if (++cache(-k).significand == 0) {
							cache(-k).significand =
								significand_type(1) << (fp_t::significand_bits - 1);
							++cache(-k).exponent;
						}
					}
					break;
				}

				cache(-k).significand <<= new_exp;
				cache(-k).significand |= significand_type(1);
			}
		}

		// Compute remaining positive powers
		for (; k <= k_max; ++k) {
			power_of_5.multiply_5();

			cache(k) = power_of_5.template get_fp<Float>();
			cache(k).exponent += k;
		}

		return ret;
	}

private:
	static constexpr std::array<fp_t, cache_size> precomputed_powers_of_10_table() {
		if constexpr (sizeof(Float) == 4) {
			return{ {
				{ 0xcad2f7f5, -128 },
				{ 0xfd87b5f3, -125 },
				{ 0x9e74d1b8, -121 },
				{ 0xc6120625, -118 },
				{ 0xf79687af, -115 },
				{ 0x9abe14cd, -111 },
				{ 0xc16d9a01, -108 },
				{ 0xf1c90081, -105 },
				{ 0x971da050, -101 },
				{ 0xbce50865, -98 },
				{ 0xec1e4a7e, -95 },
				{ 0x9392ee8f, -91 },
				{ 0xb877aa32, -88 },
				{ 0xe69594bf, -85 },
				{ 0x901d7cf7, -81 },
				{ 0xb424dc35, -78 },
				{ 0xe12e1342, -75 },
				{ 0x8cbccc09, -71 },
				{ 0xafebff0c, -68 },
				{ 0xdbe6fecf, -65 },
				{ 0x89705f41, -61 },
				{ 0xabcc7712, -58 },
				{ 0xd6bf94d6, -55 },
				{ 0x8637bd06, -51 },
				{ 0xa7c5ac47, -48 },
				{ 0xd1b71759, -45 },
				{ 0x83126e98, -41 },
				{ 0xa3d70a3d, -38 },
				{ 0xcccccccd, -35 },
				{ 0x80000000, -31 },
				{ 0xa0000000, -28 },
				{ 0xc8000000, -25 },
				{ 0xfa000000, -22 },
				{ 0x9c400000, -18 },
				{ 0xc3500000, -15 },
				{ 0xf4240000, -12 },
				{ 0x98968000, -8 },
				{ 0xbebc2000, -5 },
				{ 0xee6b2800, -2 },
				{ 0x9502f900, 2 },
				{ 0xba43b740, 5 },
				{ 0xe8d4a510, 8 },
				{ 0x9184e72a, 12 },
				{ 0xb5e620f5, 15 },
				{ 0xe35fa932, 18 },
				{ 0x8e1bc9bf, 22 },
				{ 0xb1a2bc2f, 25 },
				{ 0xde0b6b3a, 28 },
				{ 0x8ac72305, 32 },
				{ 0xad78ebc6, 35 },
				{ 0xd8d726b7, 38 },
				{ 0x87867832, 42 },
				{ 0xa968163f, 45 },
				{ 0xd3c21bcf, 48 },
				{ 0x84595161, 52 },
				{ 0xa56fa5ba, 55 },
				{ 0xcecb8f28, 58 },
				{ 0x813f3979, 62 },
				{ 0xa18f07d7, 65 },
				{ 0xc9f2c9cd, 68 },
				{ 0xfc6f7c40, 71 },
				{ 0x9dc5ada8, 75 },
				{ 0xc5371912, 78 },
				{ 0xf684df57, 81 },
				{ 0x9a130b96, 85 },
				{ 0xc097ce7c, 88 },
				{ 0xf0bdc21b, 91 },
				{ 0x96769951, 95 },
				{ 0xbc143fa5, 98 },
				{ 0xeb194f8e, 101 },
				{ 0x92efd1b9, 105 },
				{ 0xb7abc627, 108 },
				{ 0xe596b7b1, 111 },
				{ 0x8f7e32ce, 115 },
				{ 0xb35dbf82, 118 },
				{ 0xe0352f63, 121 },
				{ 0x8c213d9e, 125 },
				{ 0xaf298d05, 128 },
				{ 0xdaf3f046, 131 },
				{ 0x88d8762c, 135 },
				{ 0xab0e93b7, 138 },
				{ 0xd5d238a5, 141 },
				{ 0x85a36367, 145 },
				{ 0xa70c3c41, 148 }
			} };
		}
		else {
			static_assert(sizeof(Float) == 8);
			return{ {
				{ 0xf97ae3d0d2446f25, -1024 },
				{ 0x9becce62836ac577, -1020 },
				{ 0xc2e801fb244576d5, -1017 },
				{ 0xf3a20279ed56d48a, -1014 },
				{ 0x9845418c345644d7, -1010 },
				{ 0xbe5691ef416bd60c, -1007 },
				{ 0xedec366b11c6cb8f, -1004 },
				{ 0x94b3a202eb1c3f39, -1000 },
				{ 0xb9e08a83a5e34f08, -997 },
				{ 0xe858ad248f5c22ca, -994 },
				{ 0x91376c36d99995be, -990 },
				{ 0xb58547448ffffb2e, -987 },
				{ 0xe2e69915b3fff9f9, -984 },
				{ 0x8dd01fad907ffc3c, -980 },
				{ 0xb1442798f49ffb4b, -977 },
				{ 0xdd95317f31c7fa1d, -974 },
				{ 0x8a7d3eef7f1cfc52, -970 },
				{ 0xad1c8eab5ee43b67, -967 },
				{ 0xd863b256369d4a41, -964 },
				{ 0x873e4f75e2224e68, -960 },
				{ 0xa90de3535aaae202, -957 },
				{ 0xd3515c2831559a83, -954 },
				{ 0x8412d9991ed58092, -950 },
				{ 0xa5178fff668ae0b6, -947 },
				{ 0xce5d73ff402d98e4, -944 },
				{ 0x80fa687f881c7f8e, -940 },
				{ 0xa139029f6a239f72, -937 },
				{ 0xc987434744ac874f, -934 },
				{ 0xfbe9141915d7a922, -931 },
				{ 0x9d71ac8fada6c9b5, -927 },
				{ 0xc4ce17b399107c23, -924 },
				{ 0xf6019da07f549b2b, -921 },
				{ 0x99c102844f94e0fb, -917 },
				{ 0xc0314325637a193a, -914 },
				{ 0xf03d93eebc589f88, -911 },
				{ 0x96267c7535b763b5, -907 },
				{ 0xbbb01b9283253ca3, -904 },
				{ 0xea9c227723ee8bcb, -901 },
				{ 0x92a1958a7675175f, -897 },
				{ 0xb749faed14125d37, -894 },
				{ 0xe51c79a85916f485, -891 },
				{ 0x8f31cc0937ae58d3, -887 },
				{ 0xb2fe3f0b8599ef08, -884 },
				{ 0xdfbdcece67006ac9, -881 },
				{ 0x8bd6a141006042be, -877 },
				{ 0xaecc49914078536d, -874 },
				{ 0xda7f5bf590966849, -871 },
				{ 0x888f99797a5e012d, -867 },
				{ 0xaab37fd7d8f58179, -864 },
				{ 0xd5605fcdcf32e1d7, -861 },
				{ 0x855c3be0a17fcd26, -857 },
				{ 0xa6b34ad8c9dfc070, -854 },
				{ 0xd0601d8efc57b08c, -851 },
				{ 0x823c12795db6ce57, -847 },
				{ 0xa2cb1717b52481ed, -844 },
				{ 0xcb7ddcdda26da269, -841 },
				{ 0xfe5d54150b090b03, -838 },
				{ 0x9efa548d26e5a6e2, -834 },
				{ 0xc6b8e9b0709f109a, -831 },
				{ 0xf867241c8cc6d4c1, -828 },
				{ 0x9b407691d7fc44f8, -824 },
				{ 0xc21094364dfb5637, -821 },
				{ 0xf294b943e17a2bc4, -818 },
				{ 0x979cf3ca6cec5b5b, -814 },
				{ 0xbd8430bd08277231, -811 },
				{ 0xece53cec4a314ebe, -808 },
				{ 0x940f4613ae5ed137, -804 },
				{ 0xb913179899f68584, -801 },
				{ 0xe757dd7ec07426e5, -798 },
				{ 0x9096ea6f3848984f, -794 },
				{ 0xb4bca50b065abe63, -791 },
				{ 0xe1ebce4dc7f16dfc, -788 },
				{ 0x8d3360f09cf6e4bd, -784 },
				{ 0xb080392cc4349ded, -781 },
				{ 0xdca04777f541c568, -778 },
				{ 0x89e42caaf9491b61, -774 },
				{ 0xac5d37d5b79b6239, -771 },
				{ 0xd77485cb25823ac7, -768 },
				{ 0x86a8d39ef77164bd, -764 },
				{ 0xa8530886b54dbdec, -761 },
				{ 0xd267caa862a12d67, -758 },
				{ 0x8380dea93da4bc60, -754 },
				{ 0xa46116538d0deb78, -751 },
				{ 0xcd795be870516656, -748 },
				{ 0x806bd9714632dff6, -744 },
				{ 0xa086cfcd97bf97f4, -741 },
				{ 0xc8a883c0fdaf7df0, -738 },
				{ 0xfad2a4b13d1b5d6c, -735 },
				{ 0x9cc3a6eec6311a64, -731 },
				{ 0xc3f490aa77bd60fd, -728 },
				{ 0xf4f1b4d515acb93c, -725 },
				{ 0x991711052d8bf3c5, -721 },
				{ 0xbf5cd54678eef0b7, -718 },
				{ 0xef340a98172aace5, -715 },
				{ 0x9580869f0e7aac0f, -711 },
				{ 0xbae0a846d2195713, -708 },
				{ 0xe998d258869facd7, -705 },
				{ 0x91ff83775423cc06, -701 },
				{ 0xb67f6455292cbf08, -698 },
				{ 0xe41f3d6a7377eeca, -695 },
				{ 0x8e938662882af53e, -691 },
				{ 0xb23867fb2a35b28e, -688 },
				{ 0xdec681f9f4c31f31, -685 },
				{ 0x8b3c113c38f9f37f, -681 },
				{ 0xae0b158b4738705f, -678 },
				{ 0xd98ddaee19068c76, -675 },
				{ 0x87f8a8d4cfa417ca, -671 },
				{ 0xa9f6d30a038d1dbc, -668 },
				{ 0xd47487cc8470652b, -665 },
				{ 0x84c8d4dfd2c63f3b, -661 },
				{ 0xa5fb0a17c777cf0a, -658 },
				{ 0xcf79cc9db955c2cc, -655 },
				{ 0x81ac1fe293d599c0, -651 },
				{ 0xa21727db38cb0030, -648 },
				{ 0xca9cf1d206fdc03c, -645 },
				{ 0xfd442e4688bd304b, -642 },
				{ 0x9e4a9cec15763e2f, -638 },
				{ 0xc5dd44271ad3cdba, -635 },
				{ 0xf7549530e188c129, -632 },
				{ 0x9a94dd3e8cf578ba, -628 },
				{ 0xc13a148e3032d6e8, -625 },
				{ 0xf18899b1bc3f8ca2, -622 },
				{ 0x96f5600f15a7b7e5, -618 },
				{ 0xbcb2b812db11a5de, -615 },
				{ 0xebdf661791d60f56, -612 },
				{ 0x936b9fcebb25c996, -608 },
				{ 0xb84687c269ef3bfb, -605 },
				{ 0xe65829b3046b0afa, -602 },
				{ 0x8ff71a0fe2c2e6dc, -598 },
				{ 0xb3f4e093db73a093, -595 },
				{ 0xe0f218b8d25088b8, -592 },
				{ 0x8c974f7383725573, -588 },
				{ 0xafbd2350644eead0, -585 },
				{ 0xdbac6c247d62a584, -582 },
				{ 0x894bc396ce5da772, -578 },
				{ 0xab9eb47c81f5114f, -575 },
				{ 0xd686619ba27255a3, -572 },
				{ 0x8613fd0145877586, -568 },
				{ 0xa798fc4196e952e7, -565 },
				{ 0xd17f3b51fca3a7a1, -562 },
				{ 0x82ef85133de648c5, -558 },
				{ 0xa3ab66580d5fdaf6, -555 },
				{ 0xcc963fee10b7d1b3, -552 },
				{ 0xffbbcfe994e5c620, -549 },
				{ 0x9fd561f1fd0f9bd4, -545 },
				{ 0xc7caba6e7c5382c9, -542 },
				{ 0xf9bd690a1b68637b, -539 },
				{ 0x9c1661a651213e2d, -535 },
				{ 0xc31bfa0fe5698db8, -532 },
				{ 0xf3e2f893dec3f126, -529 },
				{ 0x986ddb5c6b3a76b8, -525 },
				{ 0xbe89523386091466, -522 },
				{ 0xee2ba6c0678b597f, -519 },
				{ 0x94db483840b717f0, -515 },
				{ 0xba121a4650e4ddec, -512 },
				{ 0xe896a0d7e51e1566, -509 },
				{ 0x915e2486ef32cd60, -505 },
				{ 0xb5b5ada8aaff80b8, -502 },
				{ 0xe3231912d5bf60e6, -499 },
				{ 0x8df5efabc5979c90, -495 },
				{ 0xb1736b96b6fd83b4, -492 },
				{ 0xddd0467c64bce4a1, -489 },
				{ 0x8aa22c0dbef60ee4, -485 },
				{ 0xad4ab7112eb3929e, -482 },
				{ 0xd89d64d57a607745, -479 },
				{ 0x87625f056c7c4a8b, -475 },
				{ 0xa93af6c6c79b5d2e, -472 },
				{ 0xd389b47879823479, -469 },
				{ 0x843610cb4bf160cc, -465 },
				{ 0xa54394fe1eedb8ff, -462 },
				{ 0xce947a3da6a9273e, -459 },
				{ 0x811ccc668829b887, -455 },
				{ 0xa163ff802a3426a9, -452 },
				{ 0xc9bcff6034c13053, -449 },
				{ 0xfc2c3f3841f17c68, -446 },
				{ 0x9d9ba7832936edc1, -442 },
				{ 0xc5029163f384a931, -439 },
				{ 0xf64335bcf065d37d, -436 },
				{ 0x99ea0196163fa42e, -432 },
				{ 0xc06481fb9bcf8d3a, -429 },
				{ 0xf07da27a82c37088, -426 },
				{ 0x964e858c91ba2655, -422 },
				{ 0xbbe226efb628afeb, -419 },
				{ 0xeadab0aba3b2dbe5, -416 },
				{ 0x92c8ae6b464fc96f, -412 },
				{ 0xb77ada0617e3bbcb, -409 },
				{ 0xe55990879ddcaabe, -406 },
				{ 0x8f57fa54c2a9eab7, -402 },
				{ 0xb32df8e9f3546564, -399 },
				{ 0xdff9772470297ebd, -396 },
				{ 0x8bfbea76c619ef36, -392 },
				{ 0xaefae51477a06b04, -389 },
				{ 0xdab99e59958885c5, -386 },
				{ 0x88b402f7fd75539b, -382 },
				{ 0xaae103b5fcd2a882, -379 },
				{ 0xd59944a37c0752a2, -376 },
				{ 0x857fcae62d8493a5, -372 },
				{ 0xa6dfbd9fb8e5b88f, -369 },
				{ 0xd097ad07a71f26b2, -366 },
				{ 0x825ecc24c8737830, -362 },
				{ 0xa2f67f2dfa90563b, -359 },
				{ 0xcbb41ef979346bca, -356 },
				{ 0xfea126b7d78186bd, -353 },
				{ 0x9f24b832e6b0f436, -349 },
				{ 0xc6ede63fa05d3144, -346 },
				{ 0xf8a95fcf88747d94, -343 },
				{ 0x9b69dbe1b548ce7d, -339 },
				{ 0xc24452da229b021c, -336 },
				{ 0xf2d56790ab41c2a3, -333 },
				{ 0x97c560ba6b0919a6, -329 },
				{ 0xbdb6b8e905cb600f, -326 },
				{ 0xed246723473e3813, -323 },
				{ 0x9436c0760c86e30c, -319 },
				{ 0xb94470938fa89bcf, -316 },
				{ 0xe7958cb87392c2c3, -313 },
				{ 0x90bd77f3483bb9ba, -309 },
				{ 0xb4ecd5f01a4aa828, -306 },
				{ 0xe2280b6c20dd5232, -303 },
				{ 0x8d590723948a535f, -299 },
				{ 0xb0af48ec79ace837, -296 },
				{ 0xdcdb1b2798182245, -293 },
				{ 0x8a08f0f8bf0f156b, -289 },
				{ 0xac8b2d36eed2dac6, -286 },
				{ 0xd7adf884aa879177, -283 },
				{ 0x86ccbb52ea94baeb, -279 },
				{ 0xa87fea27a539e9a5, -276 },
				{ 0xd29fe4b18e88640f, -273 },
				{ 0x83a3eeeef9153e89, -269 },
				{ 0xa48ceaaab75a8e2b, -266 },
				{ 0xcdb02555653131b6, -263 },
				{ 0x808e17555f3ebf12, -259 },
				{ 0xa0b19d2ab70e6ed6, -256 },
				{ 0xc8de047564d20a8c, -253 },
				{ 0xfb158592be068d2f, -250 },
				{ 0x9ced737bb6c4183d, -246 },
				{ 0xc428d05aa4751e4d, -243 },
				{ 0xf53304714d9265e0, -240 },
				{ 0x993fe2c6d07b7fac, -236 },
				{ 0xbf8fdb78849a5f97, -233 },
				{ 0xef73d256a5c0f77d, -230 },
				{ 0x95a8637627989aae, -226 },
				{ 0xbb127c53b17ec159, -223 },
				{ 0xe9d71b689dde71b0, -220 },
				{ 0x9226712162ab070e, -216 },
				{ 0xb6b00d69bb55c8d1, -213 },
				{ 0xe45c10c42a2b3b06, -210 },
				{ 0x8eb98a7a9a5b04e3, -206 },
				{ 0xb267ed1940f1c61c, -203 },
				{ 0xdf01e85f912e37a3, -200 },
				{ 0x8b61313bbabce2c6, -196 },
				{ 0xae397d8aa96c1b78, -193 },
				{ 0xd9c7dced53c72256, -190 },
				{ 0x881cea14545c7575, -186 },
				{ 0xaa242499697392d3, -183 },
				{ 0xd4ad2dbfc3d07788, -180 },
				{ 0x84ec3c97da624ab5, -176 },
				{ 0xa6274bbdd0fadd62, -173 },
				{ 0xcfb11ead453994ba, -170 },
				{ 0x81ceb32c4b43fcf5, -166 },
				{ 0xa2425ff75e14fc32, -163 },
				{ 0xcad2f7f5359a3b3e, -160 },
				{ 0xfd87b5f28300ca0e, -157 },
				{ 0x9e74d1b791e07e48, -153 },
				{ 0xc612062576589ddb, -150 },
				{ 0xf79687aed3eec551, -147 },
				{ 0x9abe14cd44753b53, -143 },
				{ 0xc16d9a0095928a27, -140 },
				{ 0xf1c90080baf72cb1, -137 },
				{ 0x971da05074da7bef, -133 },
				{ 0xbce5086492111aeb, -130 },
				{ 0xec1e4a7db69561a5, -127 },
				{ 0x9392ee8e921d5d07, -123 },
				{ 0xb877aa3236a4b449, -120 },
				{ 0xe69594bec44de15b, -117 },
				{ 0x901d7cf73ab0acd9, -113 },
				{ 0xb424dc35095cd80f, -110 },
				{ 0xe12e13424bb40e13, -107 },
				{ 0x8cbccc096f5088cc, -103 },
				{ 0xafebff0bcb24aaff, -100 },
				{ 0xdbe6fecebdedd5bf, -97 },
				{ 0x89705f4136b4a597, -93 },
				{ 0xabcc77118461cefd, -90 },
				{ 0xd6bf94d5e57a42bc, -87 },
				{ 0x8637bd05af6c69b6, -83 },
				{ 0xa7c5ac471b478423, -80 },
				{ 0xd1b71758e219652c, -77 },
				{ 0x83126e978d4fdf3b, -73 },
				{ 0xa3d70a3d70a3d70a, -70 },
				{ 0xcccccccccccccccd, -67 },
				{ 0x8000000000000000, -63 },
				{ 0xa000000000000000, -60 },
				{ 0xc800000000000000, -57 },
				{ 0xfa00000000000000, -54 },
				{ 0x9c40000000000000, -50 },
				{ 0xc350000000000000, -47 },
				{ 0xf424000000000000, -44 },
				{ 0x9896800000000000, -40 },
				{ 0xbebc200000000000, -37 },
				{ 0xee6b280000000000, -34 },
				{ 0x9502f90000000000, -30 },
				{ 0xba43b74000000000, -27 },
				{ 0xe8d4a51000000000, -24 },
				{ 0x9184e72a00000000, -20 },
				{ 0xb5e620f480000000, -17 },
				{ 0xe35fa931a0000000, -14 },
				{ 0x8e1bc9bf04000000, -10 },
				{ 0xb1a2bc2ec5000000, -7 },
				{ 0xde0b6b3a76400000, -4 },
				{ 0x8ac7230489e80000, 0 },
				{ 0xad78ebc5ac620000, 3 },
				{ 0xd8d726b7177a8000, 6 },
				{ 0x878678326eac9000, 10 },
				{ 0xa968163f0a57b400, 13 },
				{ 0xd3c21bcecceda100, 16 },
				{ 0x84595161401484a0, 20 },
				{ 0xa56fa5b99019a5c8, 23 },
				{ 0xcecb8f27f4200f3a, 26 },
				{ 0x813f3978f8940984, 30 },
				{ 0xa18f07d736b90be5, 33 },
				{ 0xc9f2c9cd04674edf, 36 },
				{ 0xfc6f7c4045812296, 39 },
				{ 0x9dc5ada82b70b59e, 43 },
				{ 0xc5371912364ce305, 46 },
				{ 0xf684df56c3e01bc7, 49 },
				{ 0x9a130b963a6c115c, 53 },
				{ 0xc097ce7bc90715b3, 56 },
				{ 0xf0bdc21abb48db20, 59 },
				{ 0x96769950b50d88f4, 63 },
				{ 0xbc143fa4e250eb31, 66 },
				{ 0xeb194f8e1ae525fd, 69 },
				{ 0x92efd1b8d0cf37be, 73 },
				{ 0xb7abc627050305ae, 76 },
				{ 0xe596b7b0c643c719, 79 },
				{ 0x8f7e32ce7bea5c70, 83 },
				{ 0xb35dbf821ae4f38c, 86 },
				{ 0xe0352f62a19e306f, 89 },
				{ 0x8c213d9da502de45, 93 },
				{ 0xaf298d050e4395d7, 96 },
				{ 0xdaf3f04651d47b4c, 99 },
				{ 0x88d8762bf324cd10, 103 },
				{ 0xab0e93b6efee0054, 106 },
				{ 0xd5d238a4abe98068, 109 },
				{ 0x85a36366eb71f041, 113 },
				{ 0xa70c3c40a64e6c52, 116 },
				{ 0xd0cf4b50cfe20766, 119 },
				{ 0x82818f1281ed44a0, 123 },
				{ 0xa321f2d7226895c8, 126 },
				{ 0xcbea6f8ceb02bb3a, 129 },
				{ 0xfee50b7025c36a08, 132 },
				{ 0x9f4f2726179a2245, 136 },
				{ 0xc722f0ef9d80aad6, 139 },
				{ 0xf8ebad2b84e0d58c, 142 },
				{ 0x9b934c3b330c8577, 146 },
				{ 0xc2781f49ffcfa6d5, 149 },
				{ 0xf316271c7fc3908b, 152 },
				{ 0x97edd871cfda3a57, 156 },
				{ 0xbde94e8e43d0c8ec, 159 },
				{ 0xed63a231d4c4fb27, 162 },
				{ 0x945e455f24fb1cf9, 166 },
				{ 0xb975d6b6ee39e437, 169 },
				{ 0xe7d34c64a9c85d44, 172 },
				{ 0x90e40fbeea1d3a4b, 176 },
				{ 0xb51d13aea4a488dd, 179 },
				{ 0xe264589a4dcdab15, 182 },
				{ 0x8d7eb76070a08aed, 186 },
				{ 0xb0de65388cc8ada8, 189 },
				{ 0xdd15fe86affad912, 192 },
				{ 0x8a2dbf142dfcc7ab, 196 },
				{ 0xacb92ed9397bf996, 199 },
				{ 0xd7e77a8f87daf7fc, 202 },
				{ 0x86f0ac99b4e8dafd, 206 },
				{ 0xa8acd7c0222311bd, 209 },
				{ 0xd2d80db02aabd62c, 212 },
				{ 0x83c7088e1aab65db, 216 },
				{ 0xa4b8cab1a1563f52, 219 },
				{ 0xcde6fd5e09abcf27, 222 },
				{ 0x80b05e5ac60b6178, 226 },
				{ 0xa0dc75f1778e39d6, 229 },
				{ 0xc913936dd571c84c, 232 },
				{ 0xfb5878494ace3a5f, 235 },
				{ 0x9d174b2dcec0e47b, 239 },
				{ 0xc45d1df942711d9a, 242 },
				{ 0xf5746577930d6501, 245 },
				{ 0x9968bf6abbe85f20, 249 },
				{ 0xbfc2ef456ae276e9, 252 },
				{ 0xefb3ab16c59b14a3, 255 },
				{ 0x95d04aee3b80ece6, 259 },
				{ 0xbb445da9ca61281f, 262 },
				{ 0xea1575143cf97227, 265 },
				{ 0x924d692ca61be758, 269 },
				{ 0xb6e0c377cfa2e12e, 272 },
				{ 0xe498f455c38b997a, 275 },
				{ 0x8edf98b59a373fec, 279 },
				{ 0xb2977ee300c50fe7, 282 },
				{ 0xdf3d5e9bc0f653e1, 285 },
				{ 0x8b865b215899f46d, 289 },
				{ 0xae67f1e9aec07188, 292 },
				{ 0xda01ee641a708dea, 295 },
				{ 0x884134fe908658b2, 299 },
				{ 0xaa51823e34a7eedf, 302 },
				{ 0xd4e5e2cdc1d1ea96, 305 },
				{ 0x850fadc09923329e, 309 },
				{ 0xa6539930bf6bff46, 312 },
				{ 0xcfe87f7cef46ff17, 315 },
				{ 0x81f14fae158c5f6e, 319 },
				{ 0xa26da3999aef774a, 322 },
				{ 0xcb090c8001ab551c, 325 },
				{ 0xfdcb4fa002162a63, 328 },
				{ 0x9e9f11c4014dda7e, 332 },
				{ 0xc646d63501a1511e, 335 },
				{ 0xf7d88bc24209a565, 338 },
				{ 0x9ae757596946075f, 342 },
				{ 0xc1a12d2fc3978937, 345 },
				{ 0xf209787bb47d6b85, 348 },
				{ 0x9745eb4d50ce6333, 352 },
				{ 0xbd176620a501fc00, 355 },
				{ 0xec5d3fa8ce427b00, 358 },
				{ 0x93ba47c980e98ce0, 362 },
				{ 0xb8a8d9bbe123f018, 365 },
				{ 0xe6d3102ad96cec1e, 368 },
				{ 0x9043ea1ac7e41393, 372 },
				{ 0xb454e4a179dd1877, 375 },
				{ 0xe16a1dc9d8545e95, 378 },
				{ 0x8ce2529e2734bb1d, 382 },
				{ 0xb01ae745b101e9e4, 385 },
				{ 0xdc21a1171d42645d, 388 },
				{ 0x899504ae72497eba, 392 },
				{ 0xabfa45da0edbde69, 395 },
				{ 0xd6f8d7509292d603, 398 },
				{ 0x865b86925b9bc5c2, 402 },
				{ 0xa7f26836f282b733, 405 },
				{ 0xd1ef0244af2364ff, 408 },
				{ 0x8335616aed761f1f, 412 },
				{ 0xa402b9c5a8d3a6e7, 415 },
				{ 0xcd036837130890a1, 418 },
				{ 0x802221226be55a65, 422 },
				{ 0xa02aa96b06deb0fe, 425 },
				{ 0xc83553c5c8965d3d, 428 },
				{ 0xfa42a8b73abbf48d, 431 },
				{ 0x9c69a97284b578d8, 435 },
				{ 0xc38413cf25e2d70e, 438 },
				{ 0xf46518c2ef5b8cd1, 441 },
				{ 0x98bf2f79d5993803, 445 },
				{ 0xbeeefb584aff8604, 448 },
				{ 0xeeaaba2e5dbf6785, 451 },
				{ 0x952ab45cfa97a0b3, 455 },
				{ 0xba756174393d88e0, 458 },
				{ 0xe912b9d1478ceb17, 461 },
				{ 0x91abb422ccb812ef, 465 },
				{ 0xb616a12b7fe617aa, 468 },
				{ 0xe39c49765fdf9d95, 471 },
				{ 0x8e41ade9fbebc27d, 475 },
				{ 0xb1d219647ae6b31c, 478 },
				{ 0xde469fbd99a05fe3, 481 },
				{ 0x8aec23d680043bee, 485 },
				{ 0xada72ccc20054aea, 488 },
				{ 0xd910f7ff28069da4, 491 },
				{ 0x87aa9aff79042287, 495 },
				{ 0xa99541bf57452b28, 498 },
				{ 0xd3fa922f2d1675f2, 501 },
				{ 0x847c9b5d7c2e09b7, 505 },
				{ 0xa59bc234db398c25, 508 },
				{ 0xcf02b2c21207ef2f, 511 },
				{ 0x8161afb94b44f57d, 515 },
				{ 0xa1ba1ba79e1632dc, 518 },
				{ 0xca28a291859bbf93, 521 },
				{ 0xfcb2cb35e702af78, 524 },
				{ 0x9defbf01b061adab, 528 },
				{ 0xc56baec21c7a1916, 531 },
				{ 0xf6c69a72a3989f5c, 534 },
				{ 0x9a3c2087a63f6399, 538 },
				{ 0xc0cb28a98fcf3c80, 541 },
				{ 0xf0fdf2d3f3c30b9f, 544 },
				{ 0x969eb7c47859e744, 548 },
				{ 0xbc4665b596706115, 551 },
				{ 0xeb57ff22fc0c795a, 554 },
				{ 0x9316ff75dd87cbd8, 558 },
				{ 0xb7dcbf5354e9bece, 561 },
				{ 0xe5d3ef282a242e82, 564 },
				{ 0x8fa475791a569d11, 568 },
				{ 0xb38d92d760ec4455, 571 },
				{ 0xe070f78d3927556b, 574 },
				{ 0x8c469ab843b89563, 578 },
				{ 0xaf58416654a6babb, 581 },
				{ 0xdb2e51bfe9d0696a, 584 },
				{ 0x88fcf317f22241e2, 588 },
				{ 0xab3c2fddeeaad25b, 591 },
				{ 0xd60b3bd56a5586f2, 594 },
				{ 0x85c7056562757457, 598 },
				{ 0xa738c6bebb12d16d, 601 },
				{ 0xd106f86e69d785c8, 604 },
				{ 0x82a45b450226b39d, 608 },
				{ 0xa34d721642b06084, 611 },
				{ 0xcc20ce9bd35c78a5, 614 },
				{ 0xff290242c83396ce, 617 },
				{ 0x9f79a169bd203e41, 621 },
				{ 0xc75809c42c684dd1, 624 },
				{ 0xf92e0c3537826146, 627 },
				{ 0x9bbcc7a142b17ccc, 631 },
				{ 0xc2abf989935ddbfe, 634 },
				{ 0xf356f7ebf83552fe, 637 },
				{ 0x98165af37b2153df, 641 },
				{ 0xbe1bf1b059e9a8d6, 644 },
				{ 0xeda2ee1c7064130c, 647 },
				{ 0x9485d4d1c63e8be8, 651 },
				{ 0xb9a74a0637ce2ee1, 654 },
				{ 0xe8111c87c5c1ba9a, 657 },
				{ 0x910ab1d4db9914a0, 661 },
				{ 0xb54d5e4a127f59c8, 664 },
				{ 0xe2a0b5dc971f303a, 667 },
				{ 0x8da471a9de737e24, 671 },
				{ 0xb10d8e1456105dad, 674 },
				{ 0xdd50f1996b947519, 677 },
				{ 0x8a5296ffe33cc930, 681 },
				{ 0xace73cbfdc0bfb7b, 684 },
				{ 0xd8210befd30efa5a, 687 },
				{ 0x8714a775e3e95c78, 691 },
				{ 0xa8d9d1535ce3b396, 694 },
				{ 0xd31045a8341ca07c, 697 },
				{ 0x83ea2b892091e44e, 701 },
				{ 0xa4e4b66b68b65d61, 704 },
				{ 0xce1de40642e3f4b9, 707 },
				{ 0x80d2ae83e9ce78f4, 711 },
				{ 0xa1075a24e4421731, 714 },
				{ 0xc94930ae1d529cfd, 717 },
				{ 0xfb9b7cd9a4a7443c, 720 },
				{ 0x9d412e0806e88aa6, 724 },
				{ 0xc491798a08a2ad4f, 727 },
				{ 0xf5b5d7ec8acb58a3, 730 },
				{ 0x9991a6f3d6bf1766, 734 },
				{ 0xbff610b0cc6edd3f, 737 },
				{ 0xeff394dcff8a948f, 740 },
				{ 0x95f83d0a1fb69cd9, 744 },
				{ 0xbb764c4ca7a44410, 747 },
				{ 0xea53df5fd18d5514, 750 },
				{ 0x92746b9be2f8552c, 754 },
				{ 0xb7118682dbb66a77, 757 },
				{ 0xe4d5e82392a40515, 760 },
				{ 0x8f05b1163ba6832d, 764 },
				{ 0xb2c71d5bca9023f8, 767 },
				{ 0xdf78e4b2bd342cf7, 770 },
				{ 0x8bab8eefb6409c1a, 774 },
				{ 0xae9672aba3d0c321, 777 },
				{ 0xda3c0f568cc4f3e9, 780 },
				{ 0x8865899617fb1871, 784 },
				{ 0xaa7eebfb9df9de8e, 787 },
				{ 0xd51ea6fa85785631, 790 },
				{ 0x8533285c936b35df, 794 },
				{ 0xa67ff273b8460357, 797 },
				{ 0xd01fef10a657842c, 800 },
				{ 0x8213f56a67f6b29c, 804 },
				{ 0xa298f2c501f45f43, 807 },
				{ 0xcb3f2f7642717713, 810 },
				{ 0xfe0efb53d30dd4d8, 813 },
				{ 0x9ec95d1463e8a507, 817 },
				{ 0xc67bb4597ce2ce49, 820 },
				{ 0xf81aa16fdc1b81db, 823 },
				{ 0x9b10a4e5e9913129, 827 },
				{ 0xc1d4ce1f63f57d73, 830 },
				{ 0xf24a01a73cf2dcd0, 833 },
				{ 0x976e41088617ca02, 837 },
				{ 0xbd49d14aa79dbc82, 840 },
				{ 0xec9c459d51852ba3, 843 },
				{ 0x93e1ab8252f33b46, 847 },
				{ 0xb8da1662e7b00a17, 850 },
				{ 0xe7109bfba19c0c9d, 853 },
				{ 0x906a617d450187e2, 857 },
				{ 0xb484f9dc9641e9db, 860 },
				{ 0xe1a63853bbd26451, 863 },
				{ 0x8d07e33455637eb3, 867 },
				{ 0xb049dc016abc5e60, 870 },
				{ 0xdc5c5301c56b75f7, 873 },
				{ 0x89b9b3e11b6329bb, 877 },
				{ 0xac2820d9623bf429, 880 },
				{ 0xd732290fbacaf134, 883 },
				{ 0x867f59a9d4bed6c0, 887 },
				{ 0xa81f301449ee8c70, 890 },
				{ 0xd226fc195c6a2f8c, 893 },
				{ 0x83585d8fd9c25db8, 897 },
				{ 0xa42e74f3d032f526, 900 },
				{ 0xcd3a1230c43fb26f, 903 },
				{ 0x80444b5e7aa7cf85, 907 },
				{ 0xa0555e361951c367, 910 },
				{ 0xc86ab5c39fa63441, 913 },
				{ 0xfa856334878fc151, 916 },
				{ 0x9c935e00d4b9d8d2, 920 },
				{ 0xc3b8358109e84f07, 923 },
				{ 0xf4a642e14c6262c9, 926 },
				{ 0x98e7e9cccfbd7dbe, 930 },
				{ 0xbf21e44003acdd2d, 933 },
				{ 0xeeea5d5004981478, 936 },
				{ 0x95527a5202df0ccb, 940 },
				{ 0xbaa718e68396cffe, 943 },
				{ 0xe950df20247c83fd, 946 },
				{ 0x91d28b7416cdd27e, 950 },
				{ 0xb6472e511c81471e, 953 },
				{ 0xe3d8f9e563a198e5, 956 },
				{ 0x8e679c2f5e44ff8f, 960 },
				{ 0xb201833b35d63f73, 963 },
				{ 0xde81e40a034bcf50, 966 },
				{ 0x8b112e86420f6192, 970 },
				{ 0xadd57a27d29339f6, 973 },
				{ 0xd94ad8b1c7380874, 976 },
				{ 0x87cec76f1c830549, 980 },
				{ 0xa9c2794ae3a3c69b, 983 },
				{ 0xd433179d9c8cb841, 986 },
				{ 0x849feec281d7f329, 990 },
				{ 0xa5c7ea73224deff3, 993 },
				{ 0xcf39e50feae16bf0, 996 },
				{ 0x81842f29f2cce376, 1000 },
				{ 0xa1e53af46f801c53, 1003 },
				{ 0xca5e89b18b602368, 1006 },
				{ 0xfcf62c1dee382c42, 1009 },
				{ 0x9e19db92b4e31ba9, 1013 },
				{ 0xc5a05277621be294, 1016 },
				{ 0xf70867153aa2db39, 1019 },
				{ 0x9a65406d44a5c903, 1023 },
				{ 0xc0fe908895cf3b44, 1026 },
				{ 0xf13e34aabb430a15, 1029 },
				{ 0x96c6e0eab509e64d, 1033 },
				{ 0xbc789925624c5fe1, 1036 },
				{ 0xeb96bf6ebadf77d9, 1039 },
				{ 0x933e37a534cbaae8, 1043 },
				{ 0xb80dc58e81fe95a1, 1046 },
				{ 0xe61136f2227e3b0a, 1049 },
				{ 0x8fcac257558ee4e6, 1053 },
				{ 0xb3bd72ed2af29e20, 1056 },
				{ 0xe0accfa875af45a8, 1059 },
				{ 0x8c6c01c9498d8b89, 1063 },
				{ 0xaf87023b9bf0ee6b, 1066 },
				{ 0xdb68c2ca82ed2a06, 1069 },
				{ 0x892179be91d43a44, 1073 }
			} };
		}
	}

	static constexpr auto powers_of_10 =
		// In theory, it is possible to evaluate this in compile-time,
		// but it will take too much compilation time to do that.
		//compute_powers_of_10();
		precomputed_powers_of_10_table();
};