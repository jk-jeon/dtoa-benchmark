#include <charconv>
#include "test.h"

void dtoa_to_chars(double value, char* buffer) {
	auto result = std::to_chars(buffer, buffer + 45, value);
	*result.ptr = '\0';
}

REGISTER_TEST(to_chars);
