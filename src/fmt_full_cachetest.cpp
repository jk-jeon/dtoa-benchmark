#define FMT_BEGIN_NAMESPACE namespace testdragonbox { namespace fmt { inline namespace v7 {
#define FMT_END_NAMESPACE }}}
#define FMT_HEADER_ONLY 1
#define FMT_USE_FULL_CACHE_DRAGONBOX 1
namespace testdragonbox {}
using namespace testdragonbox;
#include "test.h"
#include "fmt/compile.h"

void dtoa_fmt_full_cache(double value, char* buffer) {
	buffer = fmt::format_to(buffer, FMT_COMPILE("{}"), value);
	*buffer = '\0';
}

REGISTER_TEST(fmt_full_cache);