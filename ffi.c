#include <lean/lean.h>
#include <string.h>

#define intern inline static
#define l_arg b_lean_obj_arg
#define l_res lean_obj_res

intern lean_sarray_object* mk_byte_array(size_t len) {
    lean_sarray_object* o = (lean_sarray_object*)lean_alloc_object(
        sizeof(lean_sarray_object) + len
    );
    lean_set_st_header((lean_object*)o, LeanScalarArray, 1);
    o->m_size = len;
    o->m_capacity = len;
    return o;
}

void blake3(uint8_t*, size_t, uint8_t*);

extern l_res lean_byte_array_blake3(l_arg a) {
    lean_sarray_object* oa = lean_to_sarray(a);
    lean_sarray_object* res = mk_byte_array(32);
    blake3(res->m_data, oa->m_size, oa->m_data);
    return (lean_object*)res;
}
