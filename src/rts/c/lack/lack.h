#include <stdint.h>
#include <stdbool.h>

static inline bool lack_implies(bool precedent, bool consequent) {
  return !precedent || consequent;
}
