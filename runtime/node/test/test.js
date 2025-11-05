const uor = require('../index.js');
const assert = require('assert');

console.log('Testing UOR Runtime Bindings for Node.js...');

function test(name, fn) {
    try {
        fn();
        console.log(`✓ ${name}`);
    } catch (error) {
        console.error(`✗ ${name}: ${error.message}`);
        process.exit(1);
    }
}

// Test constants
test('Constants', () => {
    assert.strictEqual(uor.constants.PAGES, 48);
    assert.strictEqual(uor.constants.BYTES, 256);
    assert.strictEqual(uor.constants.RCLASSES, 96);
    assert.strictEqual(uor.constants.TOTAL_ELEMENTS, 12288);
    assert.strictEqual(uor.constants.COMPRESSION_RATIO, 0.375);
    
    assert.strictEqual(uor.getPages(), 48);
    assert.strictEqual(uor.getBytes(), 256);
    assert.strictEqual(uor.getRClasses(), 96);
});

// Test R96 classifier
test('R96 Classifier', () => {
    // Test specific values
    assert.strictEqual(uor.r96Classify(0), 0);
    assert.strictEqual(uor.r96Classify(95), 95);
    assert.strictEqual(uor.r96Classify(96), 0);
    assert.strictEqual(uor.r96Classify(255), 63);
    
    // Test range
    for (let i = 0; i <= 255; i++) {
        const result = uor.r96Classify(i);
        assert(result >= 0 && result < 96, `R96(${i}) = ${result} should be in [0,95]`);
    }
    
    // Test periodicity
    for (let i = 0; i < 96; i++) {
        assert.strictEqual(uor.r96Classify(i), uor.r96Classify(i + 96));
    }
});

// Test Phi encoding
test('Phi Encoding', () => {
    const testCases = [
        [0, 0],
        [3, 16],
        [47, 255],
        [10, 100]
    ];
    
    for (const [page, byte] of testCases) {
        const code = uor.phiEncode(page, byte);
        assert.strictEqual(uor.phiPage(code), page, `PhiPage failed for (${page}, ${byte})`);
        assert.strictEqual(uor.phiByte(code), byte, `PhiByte failed for (${page}, ${byte})`);
    }
});

// Test truth conservation
test('Truth Conservation', () => {
    assert.strictEqual(uor.truthZero(0), true);
    assert.strictEqual(uor.truthZero(1), false);
    assert.strictEqual(uor.truthZero(100), false);
    
    assert.strictEqual(uor.truthAdd(0, 0), true);
    assert.strictEqual(uor.truthAdd(1, 0), false);
    assert.strictEqual(uor.truthAdd(5, 10), false);
    
    // Test overflow
    assert.strictEqual(uor.truthAdd(0xFFFFFFFF, 1), true);
});

// Test PhiCoordinate class
test('PhiCoordinate Class', () => {
    const coord = new uor.PhiCoordinate(3, 16);
    assert.strictEqual(coord.page, 3);
    assert.strictEqual(coord.byte, 16);
    assert.strictEqual(coord.toString(), 'Φ(3,16)');
    
    const code = coord.encode();
    const decoded = uor.PhiCoordinate.decode(code);
    assert.strictEqual(decoded.page, coord.page);
    assert.strictEqual(decoded.byte, coord.byte);
    
    // Test modulo behavior
    const coord2 = new uor.PhiCoordinate(51, 44);
    assert.strictEqual(coord2.page, 3); // 51 % 48 = 3
    assert.strictEqual(coord2.byte, 44);
});

// Test ResonanceClass
test('ResonanceClass', () => {
    const rc = uor.ResonanceClass.classify(100);
    assert.strictEqual(rc.value, 4); // 100 % 96 = 4
    assert.strictEqual(rc.toString(), 'R96[4]');
    
    // Test that all 96 classes are produced
    const classes = new Set();
    for (let i = 0; i <= 255; i++) {
        classes.add(uor.ResonanceClass.classify(i).value);
    }
    assert.strictEqual(classes.size, 96);
});

// Test Conservation
test('Conservation', () => {
    assert.strictEqual(uor.Conservation.isZero(0), true);
    assert.strictEqual(uor.Conservation.isZero(42), false);
    assert.strictEqual(uor.Conservation.sumIsZero(0, 0), true);
    assert.strictEqual(uor.Conservation.sumIsZero(1, 2), false);
});

// Test PrimeStructure
test('PrimeStructure', () => {
    const ps = new uor.PrimeStructure();
    
    // Test set/get
    ps.set(5, 10, 42);
    assert.strictEqual(ps.get(5, 10), 42);
    
    // Test bounds checking
    assert.throws(() => ps.set(48, 0, 1), /out of range/);
    assert.throws(() => ps.get(48, 0), /out of range/);
    
    // Test compression stats
    const stats = ps.compressionStats();
    assert.strictEqual(stats[0], uor.constants.TOTAL_ELEMENTS - 1); // All zeros except one
    assert.strictEqual(stats[uor.r96Classify(42)], 1); // The one non-zero value
});

// Test backwards compatibility
test('Backwards Compatibility', () => {
    assert.strictEqual(typeof uor.Pages, 'function');
    assert.strictEqual(typeof uor.R96, 'function');
    assert.strictEqual(uor.Pages(), 48);
    assert.strictEqual(uor.R96(100), 4);
});

console.log('All tests passed! 🎉');