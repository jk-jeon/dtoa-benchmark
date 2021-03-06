﻿#include "test.h"
#include "jkj/grisu.h"

// The printing routine here is brought from Ryu

namespace {
	alignas(std::uint32_t) static constexpr char radix_100_table[] = {
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

	uint32_t decimalLength17(const uint64_t v) {
		// This is slightly faster than a loop.
		// The average output length is 16.38 digits, so we check high-to-low.
		// Function precondition: v is not an 18, 19, or 20-digit number.
		// (17 digits are sufficient for round-tripping.)
		assert(v < 100000000000000000L);
		if (v >= 10000000000000000L) { return 17; }
		if (v >= 1000000000000000L) { return 16; }
		if (v >= 100000000000000L) { return 15; }
		if (v >= 10000000000000L) { return 14; }
		if (v >= 1000000000000L) { return 13; }
		if (v >= 100000000000L) { return 12; }
		if (v >= 10000000000L) { return 11; }
		if (v >= 1000000000L) { return 10; }
		if (v >= 100000000L) { return 9; }
		if (v >= 10000000L) { return 8; }
		if (v >= 1000000L) { return 7; }
		if (v >= 100000L) { return 6; }
		if (v >= 10000L) { return 5; }
		if (v >= 1000L) { return 4; }
		if (v >= 100L) { return 3; }
		if (v >= 10L) { return 2; }
		return 1;
	}
}

void dtoa_jkj(double x, char* result)
{
	//print_float(x, result);

	auto v = grisu_impl<double>::grisu2(x);

	// Step 5: Print the decimal representation.
	int index = 0;
	if (v.is_negative) {
		result[index++] = '-';
	}

	uint64_t output = v.significand;
	const uint32_t olength = decimalLength17(output);

	// Print the decimal digits.
	// The following code is equivalent to:
	// for (uint32_t i = 0; i < olength - 1; ++i) {
	//   const uint32_t c = output % 10; output /= 10;
	//   result[index + olength - i] = (char) ('0' + c);
	// }
	// result[index] = '0' + output % 10;

	uint32_t i = 0;
	// We prefer 32-bit operations, even on 64-bit platforms.
	// We have at most 17 digits, and uint32_t can store 9 digits.
	// If output doesn't fit into uint32_t, we cut off 8 digits,
	// so the rest will fit into uint32_t.
	if ((output >> 32) != 0) {
		// Expensive 64-bit division.
		const uint64_t q = output / 100000000;
		uint32_t output2 = ((uint32_t)output) - 100000000 * ((uint32_t)q);
		output = q;

		const uint32_t c = output2 % 10000;
		output2 /= 10000;
		const uint32_t d = output2 % 10000;
		const uint32_t c0 = (c % 100) << 1;
		const uint32_t c1 = (c / 100) << 1;
		const uint32_t d0 = (d % 100) << 1;
		const uint32_t d1 = (d / 100) << 1;
		memcpy(result + index + olength - i - 1, radix_100_table + c0, 2);
		memcpy(result + index + olength - i - 3, radix_100_table + c1, 2);
		memcpy(result + index + olength - i - 5, radix_100_table + d0, 2);
		memcpy(result + index + olength - i - 7, radix_100_table + d1, 2);
		i += 8;
	}
	uint32_t output2 = (uint32_t)output;
	while (output2 >= 10000) {
#ifdef __clang__ // https://bugs.llvm.org/show_bug.cgi?id=38217
		const uint32_t c = output2 - 10000 * (output2 / 10000);
#else
		const uint32_t c = output2 % 10000;
#endif
		output2 /= 10000;
		const uint32_t c0 = (c % 100) << 1;
		const uint32_t c1 = (c / 100) << 1;
		memcpy(result + index + olength - i - 1, radix_100_table + c0, 2);
		memcpy(result + index + olength - i - 3, radix_100_table + c1, 2);
		i += 4;
	}
	if (output2 >= 100) {
		const uint32_t c = (output2 % 100) << 1;
		output2 /= 100;
		memcpy(result + index + olength - i - 1, radix_100_table + c, 2);
		i += 2;
	}
	if (output2 >= 10) {
		const uint32_t c = output2 << 1;
		// We can't use memcpy here: the decimal dot goes between these two digits.
		result[index + olength - i] = radix_100_table[c + 1];
		result[index] = radix_100_table[c];
	}
	else {
		result[index] = (char)('0' + output2);
	}

	// Print decimal point if needed.
	if (olength > 1) {
		result[index + 1] = '.';
		index += olength + 1;
	}
	else {
		++index;
	}

	// Print the exponent.
	result[index++] = 'e';
	int32_t exp = v.exponent + (int32_t)olength - 1;
	if (exp < 0) {
		result[index++] = '-';
		exp = -exp;
	}

	if (exp >= 100) {
		const int32_t c = exp % 10;
		memcpy(result + index, radix_100_table + 2 * (exp / 10), 2);
		result[index + 2] = (char)('0' + c);
		index += 3;
	}
	else if (exp >= 10) {
		memcpy(result + index, radix_100_table + 2 * exp, 2);
		index += 2;
	}
	else {
		result[index++] = (char)('0' + exp);
	}

	//return index;
	result[index] = '\0';
}

REGISTER_TEST(jkj);