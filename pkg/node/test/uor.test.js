const uor = require('../lib/index.js');

describe('UOR FFI Bindings', () => {
    beforeAll(() => {
        uor.initialize();
    });

    afterAll(() => {
        uor.finalize();
    });

    describe('Constants', () => {
        test('should have correct values', () => {
            expect(uor.PAGES).toBe(48);
            expect(uor.BYTES).toBe(256);
            expect(uor.RCLASSES).toBe(96);
            expect(uor.TOTAL_ELEMENTS).toBe(12288);
            expect(uor.COMPRESSION_RATIO).toBeCloseTo(3/8, 5);
        });

        test('should return correct values from functions', () => {
            expect(uor.getPages()).toBe(48);
            expect(uor.getBytes()).toBe(256);
            expect(uor.getRClasses()).toBe(96);
        });
    });

    describe('R96 Classifier', () => {
        test('should classify specific values correctly', () => {
            expect(uor.r96Classify(0)).toBe(0);
            expect(uor.r96Classify(95)).toBe(95);
            expect(uor.r96Classify(96)).toBe(0);
            expect(uor.r96Classify(255)).toBe(63);
        });

        test('should return values in valid range', () => {
            for (let i = 0; i < 256; i++) {
                const cls = uor.r96Classify(i);
                expect(cls).toBeGreaterThanOrEqual(0);
                expect(cls).toBeLessThan(96);
            }
        });

        test('should be periodic with period 96', () => {
            for (let i = 0; i < 96; i++) {
                expect(uor.r96Classify(i)).toBe(uor.r96Classify(i + 96));
            }
        });
    });

    describe('Phi Encoding', () => {
        test('should encode and decode correctly', () => {
            for (let page = 0; page < 48; page += 6) {
                for (let byte = 0; byte < 256; byte += 17) {
                    const code = uor.phiEncode(page, byte);
                    expect(uor.phiPage(code)).toBe(page);
                    expect(uor.phiByte(code)).toBe(byte);
                }
            }
        });

        test('should handle PhiCoordinate class', () => {
            const coord = new uor.PhiCoordinate(3, 16);
            expect(coord.page).toBe(3);
            expect(coord.byte).toBe(16);
            
            const code = coord.encode();
            const decoded = uor.PhiCoordinate.decode(code);
            expect(decoded.page).toBe(coord.page);
            expect(decoded.byte).toBe(coord.byte);
            expect(coord.toString()).toBe('Φ(3,16)');
        });

        test('should apply modulo correctly', () => {
            const coord = new uor.PhiCoordinate(51, 300);
            expect(coord.page).toBe(3); // 51 % 48
            expect(coord.byte).toBe(44); // 300 & 0xFF
        });
    });

    describe('Truth Conservation', () => {
        test('should check zero correctly', () => {
            expect(uor.truthZero(0)).toBe(true);
            expect(uor.truthZero(1)).toBe(false);
            expect(uor.truthZero(100)).toBe(false);
        });

        test('should check sum correctly', () => {
            expect(uor.truthAdd(0, 0)).toBe(true);
            expect(uor.truthAdd(1, 0)).toBe(false);
            expect(uor.truthAdd(5, 10)).toBe(false);
        });

        test('should handle overflow', () => {
            expect(uor.truthAdd(0xFFFFFFFF, 1)).toBe(true);
        });
    });

    describe('ResonanceClass', () => {
        test('should classify correctly', () => {
            const rc = uor.ResonanceClass.classify(100);
            expect(rc.value).toBe(4);
            expect(rc.toString()).toBe('R96[4]');
        });

        test('should produce all 96 classes', () => {
            const classes = new Set();
            for (let i = 0; i < 256; i++) {
                const rc = uor.ResonanceClass.classify(i);
                classes.add(rc.value);
            }
            expect(classes.size).toBe(96);
        });
    });

    describe('Conservation class', () => {
        test('should check conservation correctly', () => {
            expect(uor.Conservation.isZero(0)).toBe(true);
            expect(uor.Conservation.isZero(42)).toBe(false);
            expect(uor.Conservation.sumIsZero(0, 0)).toBe(true);
            expect(uor.Conservation.sumIsZero(1, 2)).toBe(false);
        });
    });
});