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
	static constexpr auto fp_t_subnormal_exponent = int(std::numeric_limits<Float>::min_exponent - significand_size - 1);

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
			mp.significand |= (sign_mask | half_unit);
			mm_significand = mp.significand - unit;
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
#elif (defined(__GNUC__) || defined(__clang__)) && defined(__SIZEOF_INT128__) && defined(__x86_64__)
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
	static constexpr int k_max = log10_pow2(alpha - fp_t::min_exponent - 1) + 1;
	static_assert(k_min < 0 && k_max > 0 && k_max >= -k_min);

	static constexpr std::size_t cache_size = k_max - k_min + 1;

	static constexpr std::size_t cache_max_bits = alpha - fp_t::min_exponent;
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

	// Currently, MSVC2019 can't compute this at compile-time
	inline static /*constexpr*/const auto powers_of_10 = compute_powers_of_10();
};