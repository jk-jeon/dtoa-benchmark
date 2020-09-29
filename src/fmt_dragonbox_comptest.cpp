#define FMT_BEGIN_NAMESPACE namespace testdragonboxcomp { namespace fmt { inline namespace v7 {
#define FMT_END_NAMESPACE }}}
#define FMT_HEADER_ONLY 1
namespace testdragonboxcomp {}
using namespace testdragonboxcomp;
#include "test.h"
#include "fmt_dragonbox_comp/compile.h"

void dtoa_fmt_dragonbox_comp(double value, char* buffer) {
	buffer = fmt::format_to(buffer, FMT_COMPILE("{}"), value);
	*buffer = '\0';
}

REGISTER_TEST(fmt_dragonbox_comp);