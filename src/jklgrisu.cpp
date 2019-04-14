#include "test.h"
#include "jkl/grisu.h"

namespace {
	alignas(std::uint32_t) static constexpr char const radix_100_table[] = {
	'0', '0', '0', '1', '0', '2', '0', '3', '0', '4',
	'0', '5', '0', '6', '0', '7', '0', '8', '0', '9',
	'1', '0', '1', '1', '1', '2', '1', '3', '1', '4',
	'1', '5', '1', '6', '1', '7', '1', '8', '1', '9',
	'2', '0', '2', '1', '2', '2', '2', '3', '2', '4',
	'2', '5', '2', '6', '2', '7', '2', '8', '2', '9',
	'3', '0', '3', '1', '3', '2', '3', '3', '3', '4',
	'3', '5', '3', '6', '3', '7', '3', '8', '3', '9',
	'4', '0', '4', '1', '4', '2', '4', '3', '4', '4',
	'4', '5', '4', '6', '4', '7', '4', '8', '4', '9',
	'5', '0', '5', '1', '5', '2', '5', '3', '5', '4',
	'5', '5', '5', '6', '5', '7', '5', '8', '5', '9',
	'6', '0', '6', '1', '6', '2', '6', '3', '6', '4',
	'6', '5', '6', '6', '6', '7', '6', '8', '6', '9',
	'7', '0', '7', '1', '7', '2', '7', '3', '7', '4',
	'7', '5', '7', '6', '7', '7', '7', '8', '7', '9',
	'8', '0', '8', '1', '8', '2', '8', '3', '8', '4',
	'8', '5', '8', '6', '8', '7', '8', '8', '8', '9',
	'9', '0', '9', '1', '9', '2', '9', '3', '9', '4',
	'9', '5', '9', '6', '9', '7', '9', '8', '9', '9'
	};

	template <class UIntType>
	char* convert_unsigned(UIntType n, char* last_letter)
	{
		auto first_letter = last_letter;

		unsigned char two_digits;
		do {
			two_digits = (unsigned char)(n % 100);
			n /= 100;
			first_letter -= 2;
			std::memcpy(first_letter, &radix_100_table[two_digits * 2], 2);
		} while (n != 0);

		return first_letter + int(two_digits < 10);
	}
}

void dtoa_jkl(double v, char* buffer)
{
	char intermediate_buffer[20];
	char* const last_letter = intermediate_buffer + sizeof(intermediate_buffer);

	auto g = grisu_impl<double>::grisu2(v);

	auto dst_ptr = buffer;
	auto src_ptr = last_letter;

	unsigned char two_digits;
	while (g.significand >= 100) {
		two_digits = (unsigned char)(g.significand % 100);
		g.significand /= 100;
		src_ptr -= 2;
		std::memcpy(src_ptr, &radix_100_table[two_digits * 2], 2);
	}

	auto written = last_letter - src_ptr;

	if (g.is_negative)
		* (dst_ptr++) = '-';

	if (g.significand < 10) {
		if (src_ptr != last_letter) {
			*(dst_ptr++) = radix_100_table[g.significand * 2 + 1];
			*(dst_ptr++) = '.';
		}
		else {
			*(dst_ptr++) = radix_100_table[g.significand * 2 + 1];
		}
	}
	else {
		*(dst_ptr++) = radix_100_table[g.significand * 2];
		*(dst_ptr++) = '.';
		*(dst_ptr++) = radix_100_table[g.significand * 2 + 1];
		++g.exponent;
	}
	std::memcpy(dst_ptr, src_ptr, written);
	dst_ptr += written;
	g.exponent += int(written);

	if (g.exponent < 0) {
		src_ptr = convert_unsigned(unsigned(-g.exponent), last_letter);
		std::memcpy(dst_ptr, "e-", 2);
		std::memcpy(dst_ptr += 2, src_ptr, last_letter - src_ptr + 1);
	}
	else if (g.exponent > 0) {
		src_ptr = convert_unsigned(unsigned(g.exponent), last_letter);
		std::memcpy(dst_ptr, "e+", 2);
		std::memcpy(dst_ptr += 2, src_ptr, last_letter - src_ptr + 1);
	}
	else
		*dst_ptr = '\0';
}

REGISTER_TEST(jkl);