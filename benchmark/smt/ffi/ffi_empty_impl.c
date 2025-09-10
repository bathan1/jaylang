#include <caml/mlvalues.h>

CAMLprim value ffi_empty(value unit) {
    return Val_unit;
}
