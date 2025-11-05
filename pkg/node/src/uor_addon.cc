#include <napi.h>
#include "uor_ffi_hybrid.h"

// Helper to convert Napi::Value to uint8_t
uint8_t AsUint8(const Napi::Value& value) {
    return static_cast<uint8_t>(value.As<Napi::Number>().Uint32Value());
}

// Helper to convert Napi::Value to uint32_t
uint32_t AsUint32(const Napi::Value& value) {
    return value.As<Napi::Number>().Uint32Value();
}

// Get number of pages
Napi::Value GetPages(const Napi::CallbackInfo& info) {
    Napi::Env env = info.Env();
    return Napi::Number::New(env, UOR_PAGES());
}

// Get bytes per page
Napi::Value GetBytes(const Napi::CallbackInfo& info) {
    Napi::Env env = info.Env();
    return Napi::Number::New(env, UOR_BYTES());
}

// Get number of resonance classes
Napi::Value GetRClasses(const Napi::CallbackInfo& info) {
    Napi::Env env = info.Env();
    return Napi::Number::New(env, UOR_RCLASSES());
}

// R96 classifier
Napi::Value R96Classify(const Napi::CallbackInfo& info) {
    Napi::Env env = info.Env();
    
    if (info.Length() < 1) {
        Napi::TypeError::New(env, "Expected 1 argument").ThrowAsJavaScriptException();
        return env.Null();
    }
    
    uint8_t b = AsUint8(info[0]);
    return Napi::Number::New(env, UOR_R96_CLASSIFY(b));
}

// Phi encode
Napi::Value PhiEncode(const Napi::CallbackInfo& info) {
    Napi::Env env = info.Env();
    
    if (info.Length() < 2) {
        Napi::TypeError::New(env, "Expected 2 arguments").ThrowAsJavaScriptException();
        return env.Null();
    }
    
    uint8_t page = AsUint8(info[0]);
    uint8_t byte = AsUint8(info[1]);
    return Napi::Number::New(env, UOR_PHI_ENCODE(page, byte));
}

// Phi page extraction
Napi::Value PhiPage(const Napi::CallbackInfo& info) {
    Napi::Env env = info.Env();
    
    if (info.Length() < 1) {
        Napi::TypeError::New(env, "Expected 1 argument").ThrowAsJavaScriptException();
        return env.Null();
    }
    
    uint32_t code = AsUint32(info[0]);
    return Napi::Number::New(env, UOR_PHI_PAGE(code));
}

// Phi byte extraction
Napi::Value PhiByte(const Napi::CallbackInfo& info) {
    Napi::Env env = info.Env();
    
    if (info.Length() < 1) {
        Napi::TypeError::New(env, "Expected 1 argument").ThrowAsJavaScriptException();
        return env.Null();
    }
    
    uint32_t code = AsUint32(info[0]);
    return Napi::Number::New(env, UOR_PHI_BYTE(code));
}

// Truth zero check
Napi::Value TruthZero(const Napi::CallbackInfo& info) {
    Napi::Env env = info.Env();
    
    if (info.Length() < 1) {
        Napi::TypeError::New(env, "Expected 1 argument").ThrowAsJavaScriptException();
        return env.Null();
    }
    
    uint32_t budget = AsUint32(info[0]);
    return Napi::Boolean::New(env, UOR_TRUTH_ZERO(budget) != 0);
}

// Truth add check
Napi::Value TruthAdd(const Napi::CallbackInfo& info) {
    Napi::Env env = info.Env();
    
    if (info.Length() < 2) {
        Napi::TypeError::New(env, "Expected 2 arguments").ThrowAsJavaScriptException();
        return env.Null();
    }
    
    uint32_t a = AsUint32(info[0]);
    uint32_t b = AsUint32(info[1]);
    return Napi::Boolean::New(env, UOR_TRUTH_ADD(a, b) != 0);
}

// Initialize function
Napi::Value Initialize(const Napi::CallbackInfo& info) {
    UOR_INIT(0);
    return info.Env().Undefined();
}

// Finalize function
Napi::Value Finalize(const Napi::CallbackInfo& info) {
    UOR_FINALIZE();
    return info.Env().Undefined();
}

// Module initialization
Napi::Object Init(Napi::Env env, Napi::Object exports) {
    // Constants
    exports.Set("PAGES", Napi::Number::New(env, 48));
    exports.Set("BYTES", Napi::Number::New(env, 256));
    exports.Set("RCLASSES", Napi::Number::New(env, 96));
    exports.Set("TOTAL_ELEMENTS", Napi::Number::New(env, 12288));
    exports.Set("COMPRESSION_RATIO", Napi::Number::New(env, 3.0 / 8.0));
    
    // Functions
    exports.Set("initialize", Napi::Function::New(env, Initialize));
    exports.Set("finalize", Napi::Function::New(env, Finalize));
    exports.Set("getPages", Napi::Function::New(env, GetPages));
    exports.Set("getBytes", Napi::Function::New(env, GetBytes));
    exports.Set("getRClasses", Napi::Function::New(env, GetRClasses));
    exports.Set("r96Classify", Napi::Function::New(env, R96Classify));
    exports.Set("phiEncode", Napi::Function::New(env, PhiEncode));
    exports.Set("phiPage", Napi::Function::New(env, PhiPage));
    exports.Set("phiByte", Napi::Function::New(env, PhiByte));
    exports.Set("truthZero", Napi::Function::New(env, TruthZero));
    exports.Set("truthAdd", Napi::Function::New(env, TruthAdd));
    
    return exports;
}

NODE_API_MODULE(uor, Init)