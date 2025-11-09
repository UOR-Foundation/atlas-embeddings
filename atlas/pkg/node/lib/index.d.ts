/**
 * TypeScript definitions for UOR FFI bindings
 */

/** Number of pages in the Prime Structure */
export const PAGES: number;

/** Number of bytes per page */
export const BYTES: number;

/** Number of resonance classes */
export const RCLASSES: number;

/** Total number of elements (12,288) */
export const TOTAL_ELEMENTS: number;

/** Compression ratio (3/8) */
export const COMPRESSION_RATIO: number;

/** Initialize the UOR library */
export function initialize(): void;

/** Finalize the UOR library */
export function finalize(): void;

/** Get the number of pages */
export function getPages(): number;

/** Get the number of bytes per page */
export function getBytes(): number;

/** Get the number of resonance classes */
export function getRClasses(): number;

/** Classify a byte into a resonance class */
export function r96Classify(byte: number): number;

/** Encode page and byte into a 32-bit code */
export function phiEncode(page: number, byte: number): number;

/** Extract page from a Phi code */
export function phiPage(code: number): number;

/** Extract byte from a Phi code */
export function phiByte(code: number): number;

/** Check if a value represents truth (zero) */
export function truthZero(budget: number): boolean;

/** Check if a sum represents truth (zero) */
export function truthAdd(a: number, b: number): boolean;

/** Decode a Phi code into page and byte */
export function phiDecode(code: number): { page: number; byte: number };

/** Get the compression ratio */
export function compressionRatio(): number;

/** Get the total number of elements */
export function totalElements(): number;

/** Phi-Atlas coordinate */
export class PhiCoordinate {
    page: number;
    byte: number;
    
    constructor(page: number, byte: number);
    encode(): number;
    static decode(code: number): PhiCoordinate;
    toString(): string;
    equals(other: PhiCoordinate): boolean;
}

/** Resonance class */
export class ResonanceClass {
    value: number;
    
    constructor(value: number);
    static classify(byte: number): ResonanceClass;
    toString(): string;
    equals(other: ResonanceClass): boolean;
}

/** Conservation checker */
export class Conservation {
    static isZero(value: number): boolean;
    static sumIsZero(a: number, b: number): boolean;
}