/*
 * UOR Runtime Python Core Extension Module
 * Enhanced Python bindings with minimal C wrapper
 */

#define PY_SSIZE_T_CLEAN
#include <Python.h>

// Include stdint for type definitions
#include <stdint.h>

// Function declarations from minimal_wrapper (using actual function names)
extern uint32_t lean_uor_pages_minimal(void);
extern uint32_t lean_uor_bytes_minimal(void);
extern uint32_t lean_uor_rclasses_minimal(void);
extern uint8_t lean_uor_r96_classify_minimal(uint8_t b);
extern uint32_t lean_uor_phi_encode_minimal(uint8_t page, uint8_t byte);
extern uint8_t lean_uor_phi_page_minimal(uint32_t code);
extern uint8_t lean_uor_phi_byte_minimal(uint32_t code);
extern uint8_t lean_uor_truth_zero_minimal(int32_t budget);
extern uint8_t lean_uor_truth_add_minimal(int32_t a, int32_t b);

// Wrapper macros for simpler names
#define uor_pages() lean_uor_pages_minimal()
#define uor_bytes() lean_uor_bytes_minimal()
#define uor_rclasses() lean_uor_rclasses_minimal()
#define uor_r96_classify(b) lean_uor_r96_classify_minimal(b)
#define uor_phi_encode(p, b) lean_uor_phi_encode_minimal(p, b)
#define uor_phi_page(c) lean_uor_phi_page_minimal(c)
#define uor_phi_byte(c) lean_uor_phi_byte_minimal(c)
#define uor_truth_zero(b) lean_uor_truth_zero_minimal(b)
#define uor_truth_add(a, b) lean_uor_truth_add_minimal(a, b)

// Module methods matching the minimal wrapper functions
static PyObject* py_pages(PyObject* self, PyObject* args) {
    return PyLong_FromLong(uor_pages());
}

static PyObject* py_bytes(PyObject* self, PyObject* args) {
    return PyLong_FromLong(uor_bytes());
}

static PyObject* py_rclasses(PyObject* self, PyObject* args) {
    return PyLong_FromLong(uor_rclasses());
}

static PyObject* py_r96_classify(PyObject* self, PyObject* args) {
    unsigned char b;
    if (!PyArg_ParseTuple(args, "b", &b)) {
        return NULL;
    }
    return PyLong_FromLong(uor_r96_classify(b));
}

static PyObject* py_phi_encode(PyObject* self, PyObject* args) {
    unsigned char page, byte;
    if (!PyArg_ParseTuple(args, "bb", &page, &byte)) {
        return NULL;
    }
    return PyLong_FromUnsignedLong(uor_phi_encode(page, byte));
}

static PyObject* py_phi_page(PyObject* self, PyObject* args) {
    unsigned int code;
    if (!PyArg_ParseTuple(args, "I", &code)) {
        return NULL;
    }
    return PyLong_FromLong(uor_phi_page(code));
}

static PyObject* py_phi_byte(PyObject* self, PyObject* args) {
    unsigned int code;
    if (!PyArg_ParseTuple(args, "I", &code)) {
        return NULL;
    }
    return PyLong_FromLong(uor_phi_byte(code));
}

static PyObject* py_truth_zero(PyObject* self, PyObject* args) {
    int budget;
    if (!PyArg_ParseTuple(args, "i", &budget)) {
        return NULL;
    }
    return PyBool_FromLong(uor_truth_zero(budget));
}

static PyObject* py_truth_add(PyObject* self, PyObject* args) {
    int a, b;
    if (!PyArg_ParseTuple(args, "ii", &a, &b)) {
        return NULL;
    }
    return PyBool_FromLong(uor_truth_add(a, b));
}

// Method definitions
static PyMethodDef module_methods[] = {
    {"pages", py_pages, METH_NOARGS, "Get number of pages (48)"},
    {"bytes", py_bytes, METH_NOARGS, "Get bytes per page (256)"},
    {"rclasses", py_rclasses, METH_NOARGS, "Get number of resonance classes (96)"},
    {"r96_classify", py_r96_classify, METH_VARARGS, "Classify byte to resonance class"},
    {"phi_encode", py_phi_encode, METH_VARARGS, "Encode page/byte coordinates"},
    {"phi_page", py_phi_page, METH_VARARGS, "Extract page from code"},
    {"phi_byte", py_phi_byte, METH_VARARGS, "Extract byte from code"},
    {"truth_zero", py_truth_zero, METH_VARARGS, "Check if budget is zero (truth)"},
    {"truth_add", py_truth_add, METH_VARARGS, "Check if sum is zero (conservation)"},
    {NULL, NULL, 0, NULL}
};

// Module definition
static struct PyModuleDef module_def = {
    PyModuleDef_HEAD_INIT,
    "_core",
    "UOR Runtime Core - Enhanced Python bindings",
    -1,
    module_methods
};

// Module initialization
PyMODINIT_FUNC PyInit__core(void) {
    return PyModule_Create(&module_def);
}