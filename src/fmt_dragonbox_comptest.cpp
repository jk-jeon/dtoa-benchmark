//#define FMT_BEGIN_NAMESPACE namespace fmt_dragonbox  {
#define FMT_HEADER_ONLY 1
#include "test.h"
#include "fmt_dragonbox_comp/compile.h"

void dtoa_fmt_dragonbox_comp(double value, char* buffer) {
	using namespace testdragonboxcomp;
	buffer = fmt::format_to(buffer, FMT_COMPILE("{}"), value);
	*buffer = '\0';
}

REGISTER_TEST(fmt_dragonbox_comp);