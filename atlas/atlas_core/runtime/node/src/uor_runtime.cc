#include <napi.h>
#include "minimal_wrapper.c"

namespace {

// Initialize the UOR runtime
Napi::Value Initialize(const Napi::CallbackInfo& info) {
    Napi::Env env = info.Env();
    lean_initialize_uor_minimal(0);
    return env.Undefined();
}

// Basic UOR functions
Napi::Value GetPages(const Napi::CallbackInfo& info) {
    Napi::Env env = info.Env();
    return Napi::Number::New(env, lean_uor_pages_minimal());
}

Napi::Value GetBytes(const Napi::CallbackInfo& info) {
    Napi::Env env = info.Env();
    return Napi::Number::New(env, lean_uor_bytes_minimal());
}

Napi::Value GetRClasses(const Napi::CallbackInfo& info) {
    Napi::Env env = info.Env();
    return Napi::Number::New(env, lean_uor_rclasses_minimal());
}

Napi::Value R96Classify(const Napi::CallbackInfo& info) {
    Napi::Env env = info.Env();
    
    if (info.Length() < 1 || !info[0].IsNumber()) {
        Napi::TypeError::New(env, "Expected number argument").ThrowAsJavaScriptException();
        return env.Undefined();
    }
    
    uint8_t b = static_cast<uint8_t>(info[0].As<Napi::Number>().Uint32Value());
    uint8_t result = lean_uor_r96_classify_minimal(b);
    return Napi::Number::New(env, result);
}

Napi::Value PhiEncode(const Napi::CallbackInfo& info) {
    Napi::Env env = info.Env();
    
    if (info.Length() < 2 || !info[0].IsNumber() || !info[1].IsNumber()) {
        Napi::TypeError::New(env, "Expected two number arguments").ThrowAsJavaScriptException();
        return env.Undefined();
    }
    
    uint8_t page = static_cast<uint8_t>(info[0].As<Napi::Number>().Uint32Value());
    uint8_t byte = static_cast<uint8_t>(info[1].As<Napi::Number>().Uint32Value());
    uint32_t result = lean_uor_phi_encode_minimal(page, byte);
    return Napi::Number::New(env, result);
}

Napi::Value PhiPage(const Napi::CallbackInfo& info) {
    Napi::Env env = info.Env();
    
    if (info.Length() < 1 || !info[0].IsNumber()) {
        Napi::TypeError::New(env, "Expected number argument").ThrowAsJavaScriptException();
        return env.Undefined();
    }
    
    uint32_t code = info[0].As<Napi::Number>().Uint32Value();
    uint8_t result = lean_uor_phi_page_minimal(code);
    return Napi::Number::New(env, result);
}

Napi::Value PhiByte(const Napi::CallbackInfo& info) {
    Napi::Env env = info.Env();
    
    if (info.Length() < 1 || !info[0].IsNumber()) {
        Napi::TypeError::New(env, "Expected number argument").ThrowAsJavaScriptException();
        return env.Undefined();
    }
    
    uint32_t code = info[0].As<Napi::Number>().Uint32Value();
    uint8_t result = lean_uor_phi_byte_minimal(code);
    return Napi::Number::New(env, result);
}

Napi::Value TruthZero(const Napi::CallbackInfo& info) {
    Napi::Env env = info.Env();
    
    if (info.Length() < 1 || !info[0].IsNumber()) {
        Napi::TypeError::New(env, "Expected number argument").ThrowAsJavaScriptException();
        return env.Undefined();
    }
    
    uint32_t budget = info[0].As<Napi::Number>().Uint32Value();
    uint8_t result = lean_uor_truth_zero_minimal(budget);
    return Napi::Boolean::New(env, result != 0);
}

Napi::Value TruthAdd(const Napi::CallbackInfo& info) {
    Napi::Env env = info.Env();
    
    if (info.Length() < 2 || !info[0].IsNumber() || !info[1].IsNumber()) {
        Napi::TypeError::New(env, "Expected two number arguments").ThrowAsJavaScriptException();
        return env.Undefined();
    }
    
    uint32_t a = info[0].As<Napi::Number>().Uint32Value();
    uint32_t b = info[1].As<Napi::Number>().Uint32Value();
    uint8_t result = lean_uor_truth_add_minimal(a, b);
    return Napi::Boolean::New(env, result != 0);
}

// Higher-level PhiCoordinate class
class PhiCoordinate : public Napi::ObjectWrap<PhiCoordinate> {
public:
    static Napi::Object Init(Napi::Env env, Napi::Object exports) {
        Napi::Function func = DefineClass(env, "PhiCoordinate", {
            InstanceMethod("encode", &PhiCoordinate::Encode),
            InstanceMethod("toString", &PhiCoordinate::ToString),
            StaticMethod("decode", &PhiCoordinate::Decode),
            InstanceAccessor("page", &PhiCoordinate::GetPage, nullptr),
            InstanceAccessor("byte", &PhiCoordinate::GetByte, nullptr)
        });
        
        constructor = Napi::Persistent(func);
        constructor.SuppressDestruct();
        exports.Set("PhiCoordinate", func);
        return exports;
    }
    
    PhiCoordinate(const Napi::CallbackInfo& info) : Napi::ObjectWrap<PhiCoordinate>(info) {
        if (info.Length() >= 2 && info[0].IsNumber() && info[1].IsNumber()) {
            page_ = static_cast<uint8_t>(info[0].As<Napi::Number>().Uint32Value()) % 48;
            byte_ = static_cast<uint8_t>(info[1].As<Napi::Number>().Uint32Value());
        } else {
            page_ = 0;
            byte_ = 0;
        }
    }

private:
    static Napi::FunctionReference constructor;
    uint8_t page_;
    uint8_t byte_;
    
    Napi::Value GetPage(const Napi::CallbackInfo& info) {
        return Napi::Number::New(info.Env(), page_);
    }
    
    Napi::Value GetByte(const Napi::CallbackInfo& info) {
        return Napi::Number::New(info.Env(), byte_);
    }
    
    Napi::Value Encode(const Napi::CallbackInfo& info) {
        Napi::Env env = info.Env();
        uint32_t code = lean_uor_phi_encode_minimal(page_, byte_);
        return Napi::Number::New(env, code);
    }
    
    Napi::Value ToString(const Napi::CallbackInfo& info) {
        Napi::Env env = info.Env();
        char buffer[32];
        snprintf(buffer, sizeof(buffer), "Φ(%d,%d)", page_, byte_);
        return Napi::String::New(env, buffer);
    }
    
    static Napi::Value Decode(const Napi::CallbackInfo& info) {
        Napi::Env env = info.Env();
        
        if (info.Length() < 1 || !info[0].IsNumber()) {
            Napi::TypeError::New(env, "Expected number argument").ThrowAsJavaScriptException();
            return env.Undefined();
        }
        
        uint32_t code = info[0].As<Napi::Number>().Uint32Value();
        uint8_t page = lean_uor_phi_page_minimal(code);
        uint8_t byte = lean_uor_phi_byte_minimal(code);
        
        return constructor.New({Napi::Number::New(env, page), Napi::Number::New(env, byte)});
    }
};

Napi::FunctionReference PhiCoordinate::constructor;

// Higher-level ResonanceClass class  
class ResonanceClass : public Napi::ObjectWrap<ResonanceClass> {
public:
    static Napi::Object Init(Napi::Env env, Napi::Object exports) {
        Napi::Function func = DefineClass(env, "ResonanceClass", {
            InstanceMethod("toString", &ResonanceClass::ToString),
            StaticMethod("classify", &ResonanceClass::Classify),
            InstanceAccessor("value", &ResonanceClass::GetValue, nullptr)
        });
        
        constructor = Napi::Persistent(func);
        constructor.SuppressDestruct();
        exports.Set("ResonanceClass", func);
        return exports;
    }
    
    ResonanceClass(const Napi::CallbackInfo& info) : Napi::ObjectWrap<ResonanceClass>(info) {
        if (info.Length() >= 1 && info[0].IsNumber()) {
            value_ = static_cast<uint8_t>(info[0].As<Napi::Number>().Uint32Value());
        } else {
            value_ = 0;
        }
    }

private:
    static Napi::FunctionReference constructor;
    uint8_t value_;
    
    Napi::Value GetValue(const Napi::CallbackInfo& info) {
        return Napi::Number::New(info.Env(), value_);
    }
    
    Napi::Value ToString(const Napi::CallbackInfo& info) {
        Napi::Env env = info.Env();
        char buffer[32];
        snprintf(buffer, sizeof(buffer), "R96[%d]", value_);
        return Napi::String::New(env, buffer);
    }
    
    static Napi::Value Classify(const Napi::CallbackInfo& info) {
        Napi::Env env = info.Env();
        
        if (info.Length() < 1 || !info[0].IsNumber()) {
            Napi::TypeError::New(env, "Expected number argument").ThrowAsJavaScriptException();
            return env.Undefined();
        }
        
        uint8_t b = static_cast<uint8_t>(info[0].As<Napi::Number>().Uint32Value());
        uint8_t rc = lean_uor_r96_classify_minimal(b);
        
        return constructor.New({Napi::Number::New(env, rc)});
    }
};

Napi::FunctionReference ResonanceClass::constructor;

// Conservation utilities
Napi::Object InitConservation(Napi::Env env) {
    Napi::Object conservation = Napi::Object::New(env);
    
    conservation.Set("isZero", Napi::Function::New(env, [](const Napi::CallbackInfo& info) -> Napi::Value {
        Napi::Env env = info.Env();
        if (info.Length() < 1 || !info[0].IsNumber()) {
            Napi::TypeError::New(env, "Expected number argument").ThrowAsJavaScriptException();
            return env.Undefined();
        }
        uint32_t value = info[0].As<Napi::Number>().Uint32Value();
        return Napi::Boolean::New(env, lean_uor_truth_zero_minimal(value) != 0);
    }));
    
    conservation.Set("sumIsZero", Napi::Function::New(env, [](const Napi::CallbackInfo& info) -> Napi::Value {
        Napi::Env env = info.Env();
        if (info.Length() < 2 || !info[0].IsNumber() || !info[1].IsNumber()) {
            Napi::TypeError::New(env, "Expected two number arguments").ThrowAsJavaScriptException();
            return env.Undefined();
        }
        uint32_t a = info[0].As<Napi::Number>().Uint32Value();
        uint32_t b = info[1].As<Napi::Number>().Uint32Value();
        return Napi::Boolean::New(env, lean_uor_truth_add_minimal(a, b) != 0);
    }));
    
    return conservation;
}

}

// Module initialization
Napi::Object Init(Napi::Env env, Napi::Object exports) {
    // Initialize the runtime
    lean_initialize_uor_minimal(0);
    
    // Constants
    Napi::Object constants = Napi::Object::New(env);
    constants.Set("PAGES", Napi::Number::New(env, 48));
    constants.Set("BYTES", Napi::Number::New(env, 256));
    constants.Set("RCLASSES", Napi::Number::New(env, 96));
    constants.Set("TOTAL_ELEMENTS", Napi::Number::New(env, 12288));
    constants.Set("COMPRESSION_RATIO", Napi::Number::New(env, 0.375));
    exports.Set("constants", constants);
    
    // Basic functions
    exports.Set("initialize", Napi::Function::New(env, Initialize));
    exports.Set("getPages", Napi::Function::New(env, GetPages));
    exports.Set("getBytes", Napi::Function::New(env, GetBytes));
    exports.Set("getRClasses", Napi::Function::New(env, GetRClasses));
    exports.Set("r96Classify", Napi::Function::New(env, R96Classify));
    exports.Set("phiEncode", Napi::Function::New(env, PhiEncode));
    exports.Set("phiPage", Napi::Function::New(env, PhiPage));
    exports.Set("phiByte", Napi::Function::New(env, PhiByte));
    exports.Set("truthZero", Napi::Function::New(env, TruthZero));
    exports.Set("truthAdd", Napi::Function::New(env, TruthAdd));
    
    // Higher-level classes
    PhiCoordinate::Init(env, exports);
    ResonanceClass::Init(env, exports);
    
    // Conservation utilities
    exports.Set("Conservation", InitConservation(env));
    
    return exports;
}

NODE_API_MODULE(uor_runtime, Init)