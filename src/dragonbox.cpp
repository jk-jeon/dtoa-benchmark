#include "test.h"
#include "dragonbox/dragonbox_to_chars.h"

void dtoa_dragonbox(double x, char* buffer)
{
	jkj::dragonbox::to_chars(x, buffer, jkj::dragonbox::policy::cache::full);
}

void dtoa_dragonbox_comp(double x, char* buffer)
{
	jkj::dragonbox::to_chars(x, buffer, jkj::dragonbox::policy::cache::compact);
}

REGISTER_TEST(dragonbox);
REGISTER_TEST(dragonbox_comp);