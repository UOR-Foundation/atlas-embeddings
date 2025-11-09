/**
 * Node.js bindings for UOR Prime Structure FFI
 * @module uor-ffi
 */

const binding = require('bindings')('uor');

// Export constants
module.exports.PAGES = binding.PAGES;
module.exports.BYTES = binding.BYTES;
module.exports.RCLASSES = binding.RCLASSES;
module.exports.TOTAL_ELEMENTS = binding.TOTAL_ELEMENTS;
module.exports.COMPRESSION_RATIO = binding.COMPRESSION_RATIO;

// Export functions
module.exports.initialize = binding.initialize;
module.exports.finalize = binding.finalize;
module.exports.getPages = binding.getPages;
module.exports.getBytes = binding.getBytes;
module.exports.getRClasses = binding.getRClasses;
module.exports.r96Classify = binding.r96Classify;
module.exports.phiEncode = binding.phiEncode;
module.exports.phiPage = binding.phiPage;
module.exports.phiByte = binding.phiByte;
module.exports.truthZero = binding.truthZero;
module.exports.truthAdd = binding.truthAdd;

/**
 * PhiCoordinate class for boundary encoding
 */
class PhiCoordinate {
    constructor(page, byte) {
        this.page = page % 48;
        this.byte = byte & 0xFF;
    }
    
    encode() {
        return binding.phiEncode(this.page, this.byte);
    }
    
    static decode(code) {
        return new PhiCoordinate(
            binding.phiPage(code),
            binding.phiByte(code)
        );
    }
    
    toString() {
        return `Φ(${this.page},${this.byte})`;
    }
    
    equals(other) {
        return other instanceof PhiCoordinate &&
               this.page === other.page &&
               this.byte === other.byte;
    }
}

module.exports.PhiCoordinate = PhiCoordinate;

/**
 * ResonanceClass for R96 classification
 */
class ResonanceClass {
    constructor(value) {
        if (value < 96) {
            this.value = value;
        } else {
            this.value = binding.r96Classify(value);
        }
    }
    
    static classify(byte) {
        return new ResonanceClass(binding.r96Classify(byte));
    }
    
    toString() {
        return `R96[${this.value}]`;
    }
    
    equals(other) {
        return other instanceof ResonanceClass &&
               this.value === other.value;
    }
}

module.exports.ResonanceClass = ResonanceClass;

/**
 * Conservation checker for truth values
 */
class Conservation {
    static isZero(value) {
        return binding.truthZero(value);
    }
    
    static sumIsZero(a, b) {
        return binding.truthAdd(a, b);
    }
}

module.exports.Conservation = Conservation;

/**
 * Helper function to decode Phi coordinates
 */
module.exports.phiDecode = function(code) {
    return {
        page: binding.phiPage(code),
        byte: binding.phiByte(code)
    };
};

/**
 * Get compression ratio as a fraction
 */
module.exports.compressionRatio = function() {
    return binding.COMPRESSION_RATIO;
};

/**
 * Get total number of elements
 */
module.exports.totalElements = function() {
    return binding.TOTAL_ELEMENTS;
};