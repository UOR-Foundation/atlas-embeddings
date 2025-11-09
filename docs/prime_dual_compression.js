/**
 * Prime-Based Dual Compression System
 * Extends Golden Compression with multiplicative canonical forms
 * 
 * Theory: Data has TWO fundamental structures:
 *   1. Additive (k-bonacci): hierarchies, nesting, composition
 *   2. Multiplicative (primes): repetition, periods, symmetries
 */

// ============================================================================
// PART 1: PRIME STRUCTURE DETECTION
// ============================================================================

class PrimeStructureDetector {
  constructor() {
    // Precompute primes up to 256 for byte analysis
    this.primes = this.sieveOfEratosthenes(256);
    this.primeIndex = new Map(this.primes.map((p, i) => [p, i]));
  }

  sieveOfEratosthenes(max) {
    const isPrime = new Array(max + 1).fill(true);
    isPrime[0] = isPrime[1] = false;
    
    for (let i = 2; i * i <= max; i++) {
      if (isPrime[i]) {
        for (let j = i * i; j <= max; j += i) {
          isPrime[j] = false;
        }
      }
    }
    
    return isPrime.reduce((primes, is, num) => {
      if (is) primes.push(num);
      return primes;
    }, []);
  }

  // Factor a number into prime powers
  primeFactorization(n) {
    const factors = new Map();
    
    for (const p of this.primes) {
      if (p * p > n) break;
      
      while (n % p === 0) {
        factors.set(p, (factors.get(p) || 0) + 1);
        n /= p;
      }
    }
    
    if (n > 1) {
      factors.set(n, 1);
    }
    
    return factors;
  }

  // Detect periodic patterns in data
  findPeriods(data, maxPeriod = null) {
    const len = data.length;
    const periods = [];
    const limit = maxPeriod || Math.floor(len / 2);
    
    for (let p = 1; p <= limit; p++) {
      const strength = this.periodStrength(data, p);
      
      if (strength > 0.7) { // 70% match threshold
        const factors = this.primeFactorization(p);
        periods.push({
          period: p,
          factors: factors,
          strength: strength,
          isPrimePeriod: factors.size === 1 && factors.values().next().value === 1
        });
      }
    }
    
    // Sort by strength
    return periods.sort((a, b) => b.strength - a.strength);
  }

  // Measure how well data fits a period
  periodStrength(data, period) {
    if (period === 0 || data.length < period * 2) return 0;
    
    let matches = 0;
    let comparisons = 0;
    
    for (let i = 0; i < data.length - period; i++) {
      if (data[i] === data[i + period]) {
        matches++;
      }
      comparisons++;
    }
    
    return matches / comparisons;
  }

  // Find divisibility patterns in byte sequences
  findDivisibilityPatterns(data) {
    const patterns = [];
    
    // Check if values follow modular arithmetic
    for (const prime of this.primes.slice(0, 10)) { // First 10 primes
      const residues = data.map(b => b % prime);
      const uniqueResidues = new Set(residues);
      
      if (uniqueResidues.size < prime * 0.5) { // Less than half possible residues
        patterns.push({
          modulus: prime,
          residues: Array.from(uniqueResidues),
          coverage: 1 - (uniqueResidues.size / prime)
        });
      }
    }
    
    return patterns.sort((a, b) => b.coverage - a.coverage);
  }

  // Detect if byte values themselves have prime structure
  findValuePrimeStructure(data) {
    const factorizations = data.map(b => ({
      value: b,
      factors: b > 1 ? this.primeFactorization(b) : new Map()
    }));
    
    // Find common prime factors across many values
    const primeOccurrences = new Map();
    
    for (const {factors} of factorizations) {
      if (factors && factors.size > 0) {
        for (const [prime, exp] of factors) {
          primeOccurrences.set(prime, (primeOccurrences.get(prime) || 0) + 1);
        }
      }
    }
    
    // Primes that appear in >30% of values are significant
    const threshold = data.length * 0.3;
    const significantPrimes = [];
    
    for (const [prime, count] of primeOccurrences) {
      if (count > threshold) {
        significantPrimes.push({
          prime,
          frequency: count / data.length
        });
      }
    }
    
    return significantPrimes.sort((a, b) => b.frequency - a.frequency);
  }

  // Main detection method
  detect(data) {
    const periods = this.findPeriods(data);
    const divisibility = this.findDivisibilityPatterns(data);
    const valueStructure = this.findValuePrimeStructure(data);
    
    return {
      hasPrimeStructure: periods.length > 0 || 
                        divisibility.length > 0 ||
                        valueStructure.length > 0,
      periods,
      divisibility,
      valueStructure,
      bestPeriod: periods[0] || null,
      primeBasis: this.extractPrimeBasis(periods, divisibility, valueStructure)
    };
  }

  extractPrimeBasis(periods, divisibility, valueStructure) {
    const basis = new Set();
    
    // From periods
    if (periods.length > 0) {
      for (const [prime] of periods[0].factors) {
        basis.add(prime);
      }
    }
    
    // From divisibility
    if (divisibility.length > 0) {
      basis.add(divisibility[0].modulus);
    }
    
    // From value structure
    if (valueStructure.length > 0) {
      basis.add(valueStructure[0].prime);
    }
    
    return Array.from(basis).sort((a, b) => a - b);
  }
}

// ============================================================================
// PART 2: K-BONACCI STRUCTURE DETECTION (from previous work)
// ============================================================================

class KBonacciStructureDetector {
  detectHierarchy(data) {
    // Simple depth analysis for structured data
    let maxDepth = 0;
    let currentDepth = 0;
    
    for (const byte of data) {
      // Opening brackets/tags increase depth
      if (byte === 0x3C || byte === 0x7B || byte === 0x5B) { // < { [
        currentDepth++;
        maxDepth = Math.max(maxDepth, currentDepth);
      }
      // Closing brackets/tags decrease depth
      else if (byte === 0x3E || byte === 0x7D || byte === 0x5D) { // > } ]
        currentDepth = Math.max(0, currentDepth - 1);
      }
    }
    
    // Optimal k is roughly related to max depth
    const optimalK = Math.min(10, Math.max(2, Math.ceil(maxDepth / 2)));
    
    return {
      maxDepth,
      optimalK,
      score: currentDepth > 0 ? 0.8 : 0.2
    };
  }
}

// ============================================================================
// PART 3: DUAL STRUCTURE ANALYZER
// ============================================================================

class DualStructureAnalyzer {
  constructor() {
    this.primeDetector = new PrimeStructureDetector();
    this.kBonacciDetector = new KBonacciStructureDetector();
  }

  analyze(data) {
    // Detect both structure types
    const additiveAnalysis = this.kBonacciDetector.detectHierarchy(data);
    const multiplicativeAnalysis = this.primeDetector.detect(data);
    
    const additiveScore = additiveAnalysis.score;
    const multiplicativeScore = multiplicativeAnalysis.hasPrimeStructure ? 0.8 : 0.2;
    
    // Determine recommendation
    let recommendation;
    if (additiveScore > 0.6 && multiplicativeScore > 0.6) {
      recommendation = 'hybrid';
    } else if (additiveScore > multiplicativeScore) {
      recommendation = 'k-bonacci';
    } else if (multiplicativeScore > 0.6) {
      recommendation = 'prime';
    } else {
      recommendation = 'none';
    }
    
    return {
      additive: {
        score: additiveScore,
        optimalK: additiveAnalysis.optimalK,
        maxDepth: additiveAnalysis.maxDepth
      },
      multiplicative: {
        score: multiplicativeScore,
        periods: multiplicativeAnalysis.periods,
        divisibility: multiplicativeAnalysis.divisibility,
        valueStructure: multiplicativeAnalysis.valueStructure,
        primeBasis: multiplicativeAnalysis.primeBasis
      },
      recommendation,
      confidence: Math.abs(additiveScore - multiplicativeScore)
    };
  }
}

// ============================================================================
// PART 4: PRIME ENCODING SCHEMES
// ============================================================================

class PrimeEncoder {
  constructor() {
    this.detector = new PrimeStructureDetector();
  }

  // Encode periodic data using period information
  encodePeriodic(data, period) {
    if (!period || data.length < period * 2) {
      return null; // Not worth encoding
    }
    
    const cycles = Math.floor(data.length / period);
    const remainder = data.length % period;
    
    // Extract the repeating cycle
    const cycle = data.slice(0, period);
    
    // Verify it actually repeats
    let matches = 0;
    for (let i = 0; i < cycles; i++) {
      const segment = data.slice(i * period, (i + 1) * period);
      if (this.arraysEqual(segment, cycle)) {
        matches++;
      }
    }
    
    const fidelity = matches / cycles;
    
    if (fidelity < 0.8) {
      return null; // Not periodic enough
    }
    
    return {
      type: 'periodic',
      period,
      periodFactors: this.detector.primeFactorization(period),
      cycle,
      repetitions: cycles,
      remainder: data.slice(cycles * period),
      fidelity,
      compressionRatio: data.length / (period + 8) // cycle + metadata
    };
  }

  // Encode using prime factorization of values
  encodeValueFactorization(data) {
    const encoded = data.map(value => {
      return {
        value,
        factors: value > 1 ? this.detector.primeFactorization(value) : new Map()
      };
    });
    
    // Check if this actually helps
    const avgFactors = encoded.reduce((sum, e) => sum + (e.factors ? e.factors.size : 0), 0) / encoded.length;
    
    return {
      type: 'value-factorization',
      encoded,
      avgFactors,
      worthwhile: avgFactors < 2 // Only useful if most numbers have few factors
    };
  }

  arraysEqual(a, b) {
    if (a.length !== b.length) return false;
    for (let i = 0; i < a.length; i++) {
      if (a[i] !== b[i]) return false;
    }
    return true;
  }
}

// ============================================================================
// PART 5: HYBRID COMPRESSION ENGINE
// ============================================================================

class DualCanonicalCompressor {
  constructor() {
    this.analyzer = new DualStructureAnalyzer();
    this.primeEncoder = new PrimeEncoder();
  }

  compress(data) {
    console.log(`\n${'='.repeat(70)}`);
    console.log('DUAL CANONICAL COMPRESSION ANALYSIS');
    console.log(`${'='.repeat(70)}\n`);
    
    console.log(`Input: ${data.length} bytes\n`);
    
    // Analyze structure
    const analysis = this.analyzer.analyze(data);
    
    console.log('STRUCTURE ANALYSIS:');
    console.log(`  Additive (k-bonacci) score: ${analysis.additive.score.toFixed(2)}`);
    console.log(`    - Max depth: ${analysis.additive.maxDepth}`);
    console.log(`    - Optimal k: ${analysis.additive.optimalK}`);
    console.log();
    console.log(`  Multiplicative (prime) score: ${analysis.multiplicative.score.toFixed(2)}`);
    console.log(`    - Periods found: ${analysis.multiplicative.periods.length}`);
    if (analysis.multiplicative.periods.length > 0) {
      console.log(`    - Best period: ${analysis.multiplicative.periods[0].period} ` +
                  `(strength: ${analysis.multiplicative.periods[0].strength.toFixed(2)})`);
    }
    console.log(`    - Prime basis: [${analysis.multiplicative.primeBasis.join(', ')}]`);
    console.log();
    console.log(`  RECOMMENDATION: ${analysis.recommendation.toUpperCase()}`);
    console.log(`  Confidence: ${analysis.confidence.toFixed(2)}`);
    console.log();
    
    // Try different encodings
    let result = {
      original: data,
      analysis,
      encodings: {}
    };
    
    // Try periodic encoding
    if (analysis.multiplicative.periods.length > 0) {
      const periodic = this.primeEncoder.encodePeriodic(
        data,
        analysis.multiplicative.periods[0].period
      );
      
      if (periodic) {
        result.encodings.periodic = periodic;
        console.log('PERIODIC ENCODING:');
        console.log(`  Period: ${periodic.period}`);
        console.log(`  Fidelity: ${(periodic.fidelity * 100).toFixed(1)}%`);
        console.log(`  Compression ratio: ${periodic.compressionRatio.toFixed(2)}:1`);
        console.log();
      }
    }
    
    // Try value factorization
    const valueFactorization = this.primeEncoder.encodeValueFactorization(data);
    result.encodings.valueFactorization = valueFactorization;
    
    if (valueFactorization.worthwhile) {
      console.log('VALUE FACTORIZATION:');
      console.log(`  Average factors per byte: ${valueFactorization.avgFactors.toFixed(2)}`);
      console.log(`  Worthwhile: ${valueFactorization.worthwhile}`);
      console.log();
    }
    
    return result;
  }
}

// ============================================================================
// PART 6: TEST SUITE
// ============================================================================

function runTests() {
  const compressor = new DualCanonicalCompressor();
  
  console.log('\n\n' + '█'.repeat(80));
  console.log('PRIME-BASED DUAL COMPRESSION: EXPERIMENTAL VALIDATION');
  console.log('█'.repeat(80));
  
  // Test 1: Pure periodic data
  console.log('\n\n' + '▓'.repeat(70));
  console.log('TEST 1: PURE PERIODIC DATA (ABABABAB...)');
  console.log('▓'.repeat(70));
  const periodic = Buffer.from('ABABABABABABABABABABABABABAB');
  compressor.compress(periodic);
  
  // Test 2: Hierarchical XML-like data
  console.log('\n\n' + '▓'.repeat(70));
  console.log('TEST 2: HIERARCHICAL DATA (nested structure)');
  console.log('▓'.repeat(70));
  const hierarchical = Buffer.from('<a><b><c>data</c></b></a>');
  compressor.compress(hierarchical);
  
  // Test 3: Hybrid data (repetition + hierarchy)
  console.log('\n\n' + '▓'.repeat(70));
  console.log('TEST 3: HYBRID DATA (repetition + hierarchy)');
  console.log('▓'.repeat(70));
  const hybrid = Buffer.from('<item>X</item><item>X</item><item>X</item><item>X</item>');
  compressor.compress(hybrid);
  
  // Test 4: Powers of 2
  console.log('\n\n' + '▓'.repeat(70));
  console.log('TEST 4: POWERS OF 2 (multiplicative structure)');
  console.log('▓'.repeat(70));
  const powers = Buffer.from([2, 4, 8, 16, 32, 64, 128, 2, 4, 8, 16, 32, 64, 128]);
  compressor.compress(powers);
  
  // Test 5: Fibonacci sequence (additive structure)
  console.log('\n\n' + '▓'.repeat(70));
  console.log('TEST 5: FIBONACCI SEQUENCE (additive structure)');
  console.log('▓'.repeat(70));
  const fibonacci = Buffer.from([1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 144]);
  compressor.compress(fibonacci);
  
  // Test 6: Highly composite numbers (lots of factors)
  console.log('\n\n' + '▓'.repeat(70));
  console.log('TEST 6: HIGHLY COMPOSITE NUMBERS');
  console.log('▓'.repeat(70));
  const composite = Buffer.from([12, 24, 36, 48, 60, 72, 84, 96, 12, 24, 36, 48]);
  compressor.compress(composite);
  
  console.log('\n\n' + '█'.repeat(80));
  console.log('END OF TESTS');
  console.log('█'.repeat(80) + '\n');
}

// ============================================================================
// EXPORTS
// ============================================================================

module.exports = {
  PrimeStructureDetector,
  KBonacciStructureDetector,
  DualStructureAnalyzer,
  PrimeEncoder,
  DualCanonicalCompressor,
  runTests
};

// Run if executed directly
if (require.main === module) {
  runTests();
}
