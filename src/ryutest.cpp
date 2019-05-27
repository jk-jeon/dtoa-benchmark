#include "ryu/ryu.h"
#include "test.h"

void dtoa_ryu(double v, char* result) {
	d2s_buffered(v, result);
}

REGISTER_TEST(ryu);