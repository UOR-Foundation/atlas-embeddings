/**
 * UOR Runtime Bindings for Node.js
 * 
 * This module provides high-level JavaScript bindings to the UOR Prime Structure
 * mathematical framework. Unlike the pkg/ bindings, this runtime version
 * provides rich classes and higher-level abstractions suitable for
 * applications that need the full power of the mathematical framework.
 */

const uorRuntime = require('./build/Release/uor_runtime');

// Initialize the runtime
uorRuntime.initialize();

// Export constants
const constants = {
    PAGES: 48,
    BYTES: 256,
    RCLASSES: 96,
    TOTAL_ELEMENTS: 12288,
    COMPRESSION_RATIO: 0.375
};

// Basic UOR functions
function getPages() {
    return uorRuntime.getPages();
}

function getBytes() {
    return uorRuntime.getBytes();
}

function getRClasses() {
    return uorRuntime.getRClasses();
}

function r96Classify(b) {
    if (typeof b !== 'number' || b < 0 || b > 255) {
        throw new Error('Byte value must be a number between 0 and 255');
    }
    return uorRuntime.r96Classify(b);
}

function phiEncode(page, byte) {
    if (typeof page !== 'number' || typeof byte !== 'number') {
        throw new Error('Page and byte must be numbers');
    }
    if (page < 0 || page >= 48 || byte < 0 || byte > 255) {
        throw new Error('Page must be 0-47, byte must be 0-255');
    }
    return uorRuntime.phiEncode(page, byte);
}

function phiPage(code) {
    if (typeof code !== 'number' || code < 0) {
        throw new Error('Code must be a non-negative number');
    }
    return uorRuntime.phiPage(code);
}

function phiByte(code) {
    if (typeof code !== 'number' || code < 0) {
        throw new Error('Code must be a non-negative number');
    }
    return uorRuntime.phiByte(code);
}

function truthZero(budget) {
    if (typeof budget !== 'number') {
        throw new Error('Budget must be a number');
    }
    return uorRuntime.truthZero(budget);
}

function truthAdd(a, b) {
    if (typeof a !== 'number' || typeof b !== 'number') {
        throw new Error('Both arguments must be numbers');
    }
    return uorRuntime.truthAdd(a, b);
}

// Enhanced PhiCoordinate wrapper
class PhiCoordinateWrapper {
    constructor(page, byte) {
        this._coord = new uorRuntime.PhiCoordinate(page, byte);
    }
    
    get page() {
        return this._coord.page;
    }
    
    get byte() {
        return this._coord.byte;
    }
    
    encode() {
        return this._coord.encode();
    }
    
    toString() {
        return this._coord.toString();
    }
    
    static decode(code) {
        const coord = uorRuntime.PhiCoordinate.decode(code);
        const wrapper = Object.create(PhiCoordinateWrapper.prototype);
        wrapper._coord = coord;
        return wrapper;
    }
}

// Enhanced ResonanceClass wrapper
class ResonanceClassWrapper {
    constructor(value) {
        this._rc = new uorRuntime.ResonanceClass(value);
    }
    
    get value() {
        return this._rc.value;
    }
    
    toString() {
        return this._rc.toString();
    }
    
    static classify(b) {
        const rc = uorRuntime.ResonanceClass.classify(b);
        const wrapper = Object.create(ResonanceClassWrapper.prototype);
        wrapper._rc = rc;
        return wrapper;
    }
}

// Conservation utilities
const Conservation = {
    isZero(value) {
        return uorRuntime.Conservation.isZero(value);
    },
    
    sumIsZero(a, b) {
        return uorRuntime.Conservation.sumIsZero(a, b);
    }
};

// PrimeStructure class for managing the full 12,288-element structure
class PrimeStructure {
    constructor() {
        this.data = Array(constants.PAGES).fill().map(() => Array(constants.BYTES).fill(0));
    }
    
    set(page, byte, value) {
        if (page < 0 || page >= constants.PAGES) {
            throw new Error(`Page ${page} out of range [0, ${constants.PAGES})`);
        }
        if (byte < 0 || byte > 255) {
            throw new Error(`Byte ${byte} out of range [0, 255]`);
        }
        if (value < 0 || value > 255) {
            throw new Error(`Value ${value} out of range [0, 255]`);
        }
        this.data[page][byte] = value;
    }
    
    get(page, byte) {
        if (page < 0 || page >= constants.PAGES) {
            throw new Error(`Page ${page} out of range [0, ${constants.PAGES})`);
        }
        if (byte < 0 || byte > 255) {
            throw new Error(`Byte ${byte} out of range [0, 255]`);
        }
        return this.data[page][byte];
    }
    
    classifyAll() {
        return this.data.map(page =>
            page.map(byte => ResonanceClassWrapper.classify(byte))
        );
    }
    
    compressionStats() {
        const stats = {};
        for (let p = 0; p < constants.PAGES; p++) {
            for (let b = 0; b < constants.BYTES; b++) {
                const rc = r96Classify(this.data[p][b]);
                stats[rc] = (stats[rc] || 0) + 1;
            }
        }
        return stats;
    }
}

// Export the API
module.exports = {
    // Constants
    constants,
    
    // Basic functions
    getPages,
    getBytes,
    getRClasses,
    r96Classify,
    phiEncode,
    phiPage,
    phiByte,
    truthZero,
    truthAdd,
    
    // Higher-level classes
    PhiCoordinate: PhiCoordinateWrapper,
    ResonanceClass: ResonanceClassWrapper,
    Conservation,
    PrimeStructure,
    
    // Backwards compatibility aliases
    Pages: getPages,
    Bytes: getBytes,
    RClasses: getRClasses,
    R96: r96Classify,
    PhiEncode: phiEncode,
    PhiPage: phiPage,
    PhiByte: phiByte,
    TruthZero: truthZero,
    TruthAdd: truthAdd
};