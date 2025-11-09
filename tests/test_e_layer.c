// atlas/tests/test_e_layer.c
// E-Layer Test Suite
// Tests for extraspecial 2-group formalization

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include "../include/e_layer.h"

// Test counter
static int tests_passed = 0;
static int tests_total = 0;

#define TEST(name) \
    do { \
        tests_total++; \
        printf("Testing " #name "... "); \
        if (test_##name()) { \
            printf("PASS\n"); \
            tests_passed++; \
        } else { \
            printf("FAIL\n"); \
        } \
    } while (0)

// ============================================================================
// Basic Group Property Tests
// ============================================================================

int test_identity_element(void) {
    EGroupElement id;
    e_group_init(&id);
    
    // Identity should have all zeros
    return (id.x_bits == 0) && (id.z_bits == 0) && (id.phase == 0);
}

int test_identity_multiplication(void) {
    EGroupElement id, x0, result;
    
    e_group_init(&id);
    e_pauli_X(&x0, 0);
    
    // id * x0 = x0
    e_group_multiply(&result, &id, &x0);
    if (!e_group_equal(&result, &x0)) return 0;
    
    // x0 * id = x0
    e_group_multiply(&result, &x0, &id);
    if (!e_group_equal(&result, &x0)) return 0;
    
    return 1;
}

int test_associativity(void) {
    EGroupElement x0, z1, x2, temp1, temp2, result1, result2;
    
    e_pauli_X(&x0, 0);
    e_pauli_Z(&z1, 1);
    e_pauli_X(&x2, 2);
    
    // (x0 * z1) * x2
    e_group_multiply(&temp1, &x0, &z1);
    e_group_multiply(&result1, &temp1, &x2);
    
    // x0 * (z1 * x2)
    e_group_multiply(&temp2, &z1, &x2);
    e_group_multiply(&result2, &x0, &temp2);
    
    return e_group_equal(&result1, &result2);
}

int test_inverse(void) {
    EGroupElement x0, inv, id, result;
    
    e_pauli_X(&x0, 0);
    e_group_inverse(&inv, &x0);
    e_group_init(&id);
    
    // x0 * x0^{-1} = id (in char 2, x0^{-1} = x0)
    e_group_multiply(&result, &x0, &inv);
    
    return e_group_equal(&result, &id);
}

// ============================================================================
// Symplectic Form Tests
// ============================================================================

int test_symplectic_alternating(void) {
    // ω(v, v) = 0 for all v
    for (int i = 0; i < 12; i++) {
        EGroupElement xi, zi;
        
        e_pauli_X(&xi, i);
        if (e_symplectic_form(&xi, &xi) != 0) return 0;
        
        e_pauli_Z(&zi, i);
        if (e_symplectic_form(&zi, &zi) != 0) return 0;
    }
    return 1;
}

int test_symplectic_antisymmetric(void) {
    // ω(v₁, v₂) = ω(v₂, v₁) in characteristic 2
    for (int i = 0; i < 4; i++) {
        for (int j = 0; j < 4; j++) {
            EGroupElement xi, zj;
            
            e_pauli_X(&xi, i);
            e_pauli_Z(&zj, j);
            
            uint8_t w12 = e_symplectic_form(&xi, &zj);
            uint8_t w21 = e_symplectic_form(&zj, &xi);
            
            if (w12 != w21) return 0;
        }
    }
    return 1;
}

int test_symplectic_x_z_same(void) {
    // ω(X_i, Z_i) = 1 (anticommute)
    for (int i = 0; i < 12; i++) {
        EGroupElement xi, zi;
        
        e_pauli_X(&xi, i);
        e_pauli_Z(&zi, i);
        
        if (e_symplectic_form(&xi, &zi) != 1) return 0;
    }
    return 1;
}

int test_symplectic_x_z_different(void) {
    // ω(X_i, Z_j) = 0 for i ≠ j (commute)
    for (int i = 0; i < 12; i++) {
        for (int j = 0; j < 12; j++) {
            if (i == j) continue;
            
            EGroupElement xi, zj;
            e_pauli_X(&xi, i);
            e_pauli_Z(&zj, j);
            
            if (e_symplectic_form(&xi, &zj) != 0) return 0;
        }
    }
    return 1;
}

// ============================================================================
// Center Tests
// ============================================================================

int test_center_is_central(void) {
    // Center elements have x=0, z=0
    EGroupElement center0, center1;
    
    e_center_element(&center0, 0);
    e_center_element(&center1, 1);
    
    if (!e_group_is_central(&center0)) return 0;
    if (!e_group_is_central(&center1)) return 0;
    
    return 1;
}

int test_center_multiplication(void) {
    // center(1) * center(1) = center(0) (since -I * -I = I in phase)
    EGroupElement c1a, c1b, c0_expected, result;
    
    e_center_element(&c1a, 1);
    e_center_element(&c1b, 1);
    e_center_element(&c0_expected, 2);  // phase 2 corresponds to -I
    
    e_group_multiply(&result, &c1a, &c1b);
    
    // After multiplication, phases add: 1+1 = 2
    return result.phase == 2;
}

int test_non_center_not_central(void) {
    // X_0 and Z_0 should not be central
    EGroupElement x0, z0;
    
    e_pauli_X(&x0, 0);
    e_pauli_Z(&z0, 0);
    
    if (e_group_is_central(&x0)) return 0;
    if (e_group_is_central(&z0)) return 0;
    
    return 1;
}

// ============================================================================
// Commutator Tests
// ============================================================================

int test_commutator_x_x(void) {
    // [X_i, X_j] = id (X's commute)
    EGroupElement x0, x1, comm, id;
    
    e_pauli_X(&x0, 0);
    e_pauli_X(&x1, 1);
    e_group_commutator(&comm, &x0, &x1);
    e_group_init(&id);
    
    return e_group_equal(&comm, &id);
}

int test_commutator_z_z(void) {
    // [Z_i, Z_j] = id (Z's commute)
    EGroupElement z0, z1, comm, id;
    
    e_pauli_Z(&z0, 0);
    e_pauli_Z(&z1, 1);
    e_group_commutator(&comm, &z0, &z1);
    e_group_init(&id);
    
    return e_group_equal(&comm, &id);
}

int test_commutator_x_z_same(void) {
    // [X_i, Z_i] = center(1) = -I (anticommute)
    for (int i = 0; i < 12; i++) {
        EGroupElement xi, zi, comm, center_expected;
        
        e_pauli_X(&xi, i);
        e_pauli_Z(&zi, i);
        e_group_commutator(&comm, &xi, &zi);
        e_center_element(&center_expected, 2);  // phase 2 = -I
        
        if (!e_group_equal(&comm, &center_expected)) return 0;
    }
    return 1;
}

int test_commutator_x_z_different(void) {
    // [X_i, Z_j] = id for i ≠ j (commute)
    EGroupElement x0, z1, comm, id;
    
    e_pauli_X(&x0, 0);
    e_pauli_Z(&z1, 1);
    e_group_commutator(&comm, &x0, &z1);
    e_group_init(&id);
    
    return e_group_equal(&comm, &id);
}

int test_commutator_is_central(void) {
    // All commutators should be central elements
    for (int i = 0; i < 4; i++) {
        for (int j = 0; j < 4; j++) {
            EGroupElement xi, zj, comm;
            
            e_pauli_X(&xi, i);
            e_pauli_Z(&zj, j);
            e_group_commutator(&comm, &xi, &zj);
            
            if (!e_group_is_central(&comm)) return 0;
        }
    }
    return 1;
}

// ============================================================================
// Pauli Basis Tests
// ============================================================================

int test_pauli_x_squared(void) {
    // X_i^2 = id (order 2)
    for (int i = 0; i < 12; i++) {
        EGroupElement xi, result, id;
        
        e_pauli_X(&xi, i);
        e_group_multiply(&result, &xi, &xi);
        e_group_init(&id);
        
        if (!e_group_equal(&result, &id)) return 0;
    }
    return 1;
}

int test_pauli_z_squared(void) {
    // Z_i^2 = id (order 2)
    for (int i = 0; i < 12; i++) {
        EGroupElement zi, result, id;
        
        e_pauli_Z(&zi, i);
        e_group_multiply(&result, &zi, &zi);
        e_group_init(&id);
        
        if (!e_group_equal(&result, &id)) return 0;
    }
    return 1;
}

int test_pauli_x_z_commute_different(void) {
    // X_i * Z_j = Z_j * X_i for i ≠ j
    EGroupElement x0, z1, prod1, prod2;
    
    e_pauli_X(&x0, 0);
    e_pauli_Z(&z1, 1);
    
    e_group_multiply(&prod1, &x0, &z1);
    e_group_multiply(&prod2, &z1, &x0);
    
    return e_group_equal(&prod1, &prod2);
}

// ============================================================================
// Quotient Tests
// ============================================================================

int test_quotient_projection(void) {
    EGroupElement x0;
    uint64_t x_out, z_out;
    
    e_pauli_X(&x0, 0);
    e_quotient_project(&x0, &x_out, &z_out);
    
    return (x_out == (1ULL << 0)) && (z_out == 0);
}

int test_from_quotient(void) {
    EGroupElement elem;
    uint64_t x = 0x123;
    uint64_t z = 0x456;
    
    e_from_quotient(&elem, x, z);
    
    return (elem.x_bits == x) && (elem.z_bits == z) && (elem.phase == 0);
}

// ============================================================================
// Verification Tests
// ============================================================================

int test_verify_group_axioms(void) {
    return e_verify_group_axioms();
}

int test_verify_commutation_relations(void) {
    return e_verify_commutation_relations();
}

int test_verify_alternating(void) {
    return e_verify_alternating();
}

int test_verify_antisymmetric(void) {
    return e_verify_antisymmetric();
}

int test_verify_atlas_connection(void) {
    return e_verify_atlas_connection();
}

// ============================================================================
// State Vector Tests
// ============================================================================

int test_state_vector_identity(void) {
    // Applying identity should leave state unchanged
    double state[4] = {1.0, 0.0, 0.0, 0.0};
    double expected[4] = {1.0, 0.0, 0.0, 0.0};
    
    EGroupElement id;
    e_group_init(&id);
    e_group_apply_to_state(&id, state, 4);
    
    for (int i = 0; i < 4; i++) {
        if (state[i] != expected[i]) return 0;
    }
    return 1;
}

int test_state_vector_x_operator(void) {
    // X_0 flips bit 0: |0⟩ -> |1⟩
    double state[2] = {1.0, 0.0};
    double expected[2] = {0.0, 1.0};
    
    EGroupElement x0;
    e_pauli_X(&x0, 0);
    e_group_apply_to_state(&x0, state, 2);
    
    for (int i = 0; i < 2; i++) {
        if (state[i] != expected[i]) return 0;
    }
    return 1;
}

int test_state_vector_z_operator(void) {
    // Z_0 adds phase: |1⟩ -> -|1⟩
    double state[2] = {0.0, 1.0};
    double expected[2] = {0.0, -1.0};
    
    EGroupElement z0;
    e_pauli_Z(&z0, 0);
    e_group_apply_to_state(&z0, state, 2);
    
    for (int i = 0; i < 2; i++) {
        if (state[i] != expected[i]) return 0;
    }
    return 1;
}

// ============================================================================
// Main Test Runner
// ============================================================================

int main(void) {
    printf("=== E-Layer Test Suite ===\n\n");
    
    printf("Basic Group Properties:\n");
    TEST(identity_element);
    TEST(identity_multiplication);
    TEST(associativity);
    TEST(inverse);
    
    printf("\nSymplectic Form:\n");
    TEST(symplectic_alternating);
    TEST(symplectic_antisymmetric);
    TEST(symplectic_x_z_same);
    TEST(symplectic_x_z_different);
    
    printf("\nCenter:\n");
    TEST(center_is_central);
    TEST(center_multiplication);
    TEST(non_center_not_central);
    
    printf("\nCommutators:\n");
    TEST(commutator_x_x);
    TEST(commutator_z_z);
    TEST(commutator_x_z_same);
    TEST(commutator_x_z_different);
    TEST(commutator_is_central);
    
    printf("\nPauli Basis:\n");
    TEST(pauli_x_squared);
    TEST(pauli_z_squared);
    TEST(pauli_x_z_commute_different);
    
    printf("\nQuotient:\n");
    TEST(quotient_projection);
    TEST(from_quotient);
    
    printf("\nVerification:\n");
    TEST(verify_group_axioms);
    TEST(verify_commutation_relations);
    TEST(verify_alternating);
    TEST(verify_antisymmetric);
    TEST(verify_atlas_connection);
    
    printf("\nState Vector:\n");
    TEST(state_vector_identity);
    TEST(state_vector_x_operator);
    TEST(state_vector_z_operator);
    
    printf("\n=== Test Results ===\n");
    printf("Passed: %d/%d\n", tests_passed, tests_total);
    
    if (tests_passed == tests_total) {
        printf("SUCCESS: All tests passed!\n");
        return 0;
    } else {
        printf("FAILURE: Some tests failed.\n");
        return 1;
    }
}
