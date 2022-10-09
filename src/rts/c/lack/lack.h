#include <stdint.h>
#include <stdbool.h>

#include <math.h>

/** Base types: give reals a scary name for now because of the logic gap
 * between reals and floats. */
typedef float float32_unsound_t;

bool lack_float_approx(float32_unsound_t a, float32_unsound_t b) {
  float32_unsound_t diff = fabs(a - b);
  float32_unsound_t max = fmax(fabs(a), fabs(b));
  float32_unsound_t eps = 1e-7f;
  float32_unsound_t diffx = max == 0 ? eps : diff / max;

  return fabs(diffx) < eps || (fabs(a) < eps && fabs(b) < eps);
}

/** Logical connectives */
static inline bool lack_implies(bool precedent, bool consequent) {
  return !precedent || consequent;
}

/** Safe division returns 0 for division-by-zero, as in Isabelle and SMT-lib */
#define LACK_DIV(t)         \
  static inline t           \
  lack_div_ ## t(t a, t b) {\
    if (b == 0)             \
      return 0;             \
    else                    \
      return a / b;         \
  }

LACK_DIV(int8_t)
LACK_DIV(uint8_t)
LACK_DIV(int16_t)
LACK_DIV(uint16_t)
LACK_DIV(int32_t)
LACK_DIV(uint32_t)
LACK_DIV(int64_t)
LACK_DIV(uint64_t)
LACK_DIV(float32_unsound_t)
