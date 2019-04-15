#include "test.h"
#include "milo/dtoa_milo.h"

void dtoa_milo_only_Grisu2(double value, char* buffer) {
	int length, K;
	Grisu2(value, buffer, &length, &K);
}

REGISTER_TEST(milo_only_Grisu2);
