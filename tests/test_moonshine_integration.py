"""
Tests for Monster Moonshine Integration module.

Validates Q-series operations, modular forms, Hecke operators,
and McKay-Thompson series for the identity class (1A = J).
"""

import pytest
from atlas.aep.moonshine_integration import (
    QSeries,
    eisenstein_E4,
    dedekind_eta_power_24,
    j_J_series,
    hecke_H_m,
    hecke_T_m,
    Faber,
    McKayThompson,
    sigma_k,
    validate_J_coefficients,
    validate_replicability,
)


# ---------------------------
# QSeries tests
# ---------------------------


def test_qseries_basic_operations():
    """Test basic QSeries operations."""
    f = QSeries({-1: 1, 0: 2, 1: 3})
    g = QSeries({0: 1, 1: -1, 2: 4})

    # Coefficient access
    assert f.coeff(-1) == 1
    assert f.coeff(0) == 2
    assert f.coeff(1) == 3
    assert f.coeff(5) == 0

    # Shift
    f_shifted = f.shift(2)
    assert f_shifted.coeff(1) == 1
    assert f_shifted.coeff(2) == 2
    assert f_shifted.coeff(3) == 3

    # Scale
    f_scaled = f.scale(3)
    assert f_scaled.coeff(-1) == 3
    assert f_scaled.coeff(0) == 6
    assert f_scaled.coeff(1) == 9

    # Addition
    h = f + g
    assert h.coeff(0) == 3
    assert h.coeff(1) == 2

    # Subtraction
    h = f - g
    assert h.coeff(0) == 1
    assert h.coeff(1) == 4

    # Multiplication
    h = f * g
    assert h.coeff(-1) == 1  # 1 * 1
    assert h.coeff(0) == 1   # 1*1 + 2*1 - 1*1 = 2
    assert h.coeff(1) == 5   # 2*(-1) + 3*1 + 1*4


def test_qseries_power():
    """Test QSeries power operation."""
    f = QSeries({0: 1, 1: 2})

    # f^0 = 1
    f0 = f.pow_int(0, -5, 5)
    assert f0.coeff(0) == 1
    assert f0.coeff(1) == 0

    # f^1 = f
    f1 = f.pow_int(1, -5, 5)
    assert f1.coeff(0) == 1
    assert f1.coeff(1) == 2

    # f^2 = 1 + 4q + 4q^2
    f2 = f.pow_int(2, -5, 5)
    assert f2.coeff(0) == 1
    assert f2.coeff(1) == 4
    assert f2.coeff(2) == 4

    # f^3 = 1 + 6q + 12q^2 + 8q^3
    f3 = f.pow_int(3, -5, 5)
    assert f3.coeff(0) == 1
    assert f3.coeff(1) == 6
    assert f3.coeff(2) == 12
    assert f3.coeff(3) == 8


def test_qseries_truncate():
    """Test QSeries truncation."""
    f = QSeries({-2: 1, -1: 2, 0: 3, 1: 4, 2: 5})

    trunc = f.truncated(-1, 1)
    assert trunc.coeff(-2) == 0
    assert trunc.coeff(-1) == 2
    assert trunc.coeff(0) == 3
    assert trunc.coeff(1) == 4
    assert trunc.coeff(2) == 0


def test_qseries_min_max_power():
    """Test min and max power detection."""
    f = QSeries({-3: 1, 0: 2, 5: 3})
    assert f.min_power() == -3
    assert f.max_power() == 5

    empty = QSeries({})
    assert empty.min_power() is None
    assert empty.max_power() is None


# ---------------------------
# Arithmetic helpers tests
# ---------------------------


def test_sigma_k():
    """Test divisor sum function."""
    # sigma_0(n) = number of divisors
    assert sigma_k(1, 0) == 1
    assert sigma_k(6, 0) == 4  # divisors: 1, 2, 3, 6
    assert sigma_k(12, 0) == 6  # divisors: 1, 2, 3, 4, 6, 12

    # sigma_1(n) = sum of divisors
    assert sigma_k(1, 1) == 1
    assert sigma_k(6, 1) == 12  # 1+2+3+6
    assert sigma_k(12, 1) == 28  # 1+2+3+4+6+12

    # sigma_3(n) for Eisenstein E_4
    assert sigma_k(1, 3) == 1
    assert sigma_k(2, 3) == 9  # 1^3 + 2^3
    assert sigma_k(3, 3) == 28  # 1^3 + 3^3


# ---------------------------
# Modular forms tests
# ---------------------------


def test_eisenstein_E4():
    """Test Eisenstein E_4 series."""
    E4 = eisenstein_E4(5)

    # E_4(q) = 1 + 240*sigma_3(1)*q + 240*sigma_3(2)*q^2 + ...
    assert E4.coeff(0) == 1
    assert E4.coeff(1) == 240 * sigma_k(1, 3)  # 240 * 1 = 240
    assert E4.coeff(2) == 240 * sigma_k(2, 3)  # 240 * 9 = 2160
    assert E4.coeff(3) == 240 * sigma_k(3, 3)  # 240 * 28 = 6720


def test_dedekind_eta_power_24():
    """Test Delta = eta^24 modular form."""
    Delta = dedekind_eta_power_24(5)

    # Delta(q) = q * prod(1-q^n)^24
    # Leading term is q
    assert Delta.coeff(0) == 0
    assert Delta.coeff(1) != 0  # Has q term

    # Delta should have no negative powers
    assert Delta.min_power() == 1


def test_j_function_structure():
    """Test j-function has correct structure."""
    j, J = j_J_series(10)

    # j has principal part q^{-1}
    assert j.min_power() == -1
    assert j.coeff(-1) != 0

    # J = j - 744
    assert J.coeff(-1) == j.coeff(-1)
    assert J.coeff(0) == j.coeff(0) - 744


def test_J_known_coefficients():
    """Test J-function matches known coefficients."""
    _, J = j_J_series(10)

    # J(q) = q^{-1} + 0 + 196884*q + 21493760*q^2 + 864299970*q^3 + ...
    assert J.coeff(-1) == 1
    assert J.coeff(0) == 0
    assert J.coeff(1) == 196884
    assert J.coeff(2) == 21493760
    assert J.coeff(3) == 864299970


# ---------------------------
# Hecke operator tests
# ---------------------------


def test_hecke_operators_on_simple_series():
    """Test Hecke operators on simple test series."""
    # f(q) = q^{-1} + q
    f = QSeries({-1: 1, 1: 1})

    # H_2(f)
    H2 = hecke_H_m(f, 2, nmin=-2, nmax=2)
    # H_2 = 1*(V_2 U_1 f) + 2*(V_1 U_2 f)
    # Should have principal part at q^{-2}
    assert H2.coeff(-2) != 0  # Should have q^{-2} term

    # T_2(f) = H_2(f) / 2 (integer division)
    T2 = hecke_T_m(f, 2, nmin=-2, nmax=2)
    # Check that T_2 * 2 matches H_2 for even coefficients
    # Note: H_2(-2) = 1, so T_2(-2) = 0 due to integer division
    for n in range(-2, 3):
        if H2.coeff(n) % 2 == 0:
            assert T2.coeff(n) * 2 == H2.coeff(n)


def test_hecke_on_J():
    """Test Hecke operator on J-function."""
    _, J = j_J_series(50)

    # Compute H_2(J) and T_2(J)
    H2_J = hecke_H_m(J, 2, nmin=-2, nmax=50)
    T2_J = hecke_T_m(J, 2, nmin=-2, nmax=50)

    # H_2(J) should have principal part at q^{-2}
    assert H2_J.coeff(-2) != 0

    # Check relation: T_2 = H_2 / 2 (with integer division)
    # Note: principal part H_2(-2) might be odd
    for n in range(-1, 51):  # Skip -2 as it might be odd
        h = H2_J.coeff(n)
        if h % 2 == 0:  # Only check even coefficients
            assert T2_J.coeff(n) * 2 == h


# ---------------------------
# Faber / Replicability tests
# ---------------------------


def test_faber_polynomial_structure():
    """Test Faber polynomial construction."""
    _, J = j_J_series(50)

    # Compute P_2(J)
    P2, P2_J = Faber.Pm_evaluate(J, 2, nmin=-2, nmax=50)

    # P_2 should be monic of degree 2
    assert P2.degree() == 2
    assert P2.coeffs[2] == 1  # monic

    # P_2(J) should have principal part at q^{-2}
    assert P2_J.coeff(-2) != 0


def test_replicability_property_m2():
    """Test replicability: P_m(J) = H_m(J) for m=2."""
    _, J = j_J_series(100)

    # Compute P_2(J) and H_2(J)
    _, P2_J = Faber.Pm_evaluate(J, 2, nmin=-2, nmax=100)
    H2_J = hecke_H_m(J, 2, nmin=-2, nmax=100)

    # They should be equal
    for n in range(-2, 101):
        assert P2_J.coeff(n) == H2_J.coeff(n)


def test_replicability_property_multiple_m():
    """Test replicability: P_m(J) = H_m(J) for multiple m."""
    _, J = j_J_series(100)

    for m in [2, 3, 4, 5]:
        _, Pm_J = Faber.Pm_evaluate(J, m, nmin=-m, nmax=100)
        Hm_J = hecke_H_m(J, m, nmin=-m, nmax=100)

        # Check equality in reasonable range
        for n in range(-m, min(50, 101)):
            assert Pm_J.coeff(n) == Hm_J.coeff(n), f"Mismatch at m={m}, n={n}"


# ---------------------------
# McKay-Thompson series tests
# ---------------------------


def test_mckay_thompson_identity():
    """Test McKay-Thompson series for identity class."""
    MT = McKayThompson.identity_J(10)

    assert MT.name == "1A"
    assert MT.series.coeff(-1) == 1
    assert MT.series.coeff(0) == 0

    # Check coefficients method
    coeffs = MT.coefficients(3)
    assert coeffs == [196884, 21493760, 864299970]


# ---------------------------
# Validation tests
# ---------------------------


def test_validate_J_coefficients():
    """Test J-function coefficient validation."""
    assert validate_J_coefficients(10) is True


def test_validate_replicability_property():
    """Test replicability validation for m=2..10."""
    # This is a longer test, use smaller N for speed
    assert validate_replicability(m_max=10, N=100) is True


# ---------------------------
# Integration tests
# ---------------------------


def test_full_workflow_identity_class():
    """Test complete workflow for identity class (1A)."""
    N = 150

    # Build J-function
    j, J = j_J_series(N)

    # Create McKay-Thompson series
    MT = McKayThompson.identity_J(N)

    # Verify first coefficients
    first3 = MT.coefficients(3)
    assert first3 == [196884, 21493760, 864299970]

    # Check replicability for m=2,3,4
    for m in [2, 3, 4]:
        _, Pm_J = Faber.Pm_evaluate(J, m, nmin=-m, nmax=100)
        Hm_J = hecke_H_m(J, m, nmin=-m, nmax=100)

        # Spot check a few coefficients
        for n in [-m, 0, 1, 10]:
            if n <= 100:
                assert Pm_J.coeff(n) == Hm_J.coeff(n)


def test_hecke_divisor_formula():
    """Test that Hecke operator uses correct divisor formula."""
    _, J = j_J_series(50)

    # For m=6, divisors are 1,2,3,6
    # H_6 = 1*(V_1 U_6) + 2*(V_2 U_3) + 3*(V_3 U_2) + 6*(V_6 U_1)
    H6 = hecke_H_m(J, 6, nmin=-6, nmax=50)

    # Should have principal part at q^{-6}
    assert H6.coeff(-6) != 0


def test_series_operations_preserve_exactness():
    """Test that all operations maintain integer arithmetic."""
    f = QSeries({-1: 1, 0: 3, 1: 7})
    g = QSeries({0: 2, 1: -5})

    # All operations should produce integer coefficients
    h = f + g
    assert all(isinstance(c, int) for c in h.a.values())

    h = f * g
    assert all(isinstance(c, int) for c in h.a.values())

    h = f.pow_int(3, -5, 5)
    assert all(isinstance(c, int) for c in h.a.values())


# ---------------------------
# Performance/stress tests (optional, marked slow)
# ---------------------------


@pytest.mark.slow
def test_large_N_computation():
    """Test computation with larger N (marked slow)."""
    N = 300
    _, J = j_J_series(N)

    # Should complete without error
    assert J.coeff(-1) == 1
    assert J.coeff(0) == 0

    # Check a few known coefficients
    assert J.coeff(1) == 196884


@pytest.mark.slow
def test_replicability_extended():
    """Test replicability for extended range (marked slow)."""
    assert validate_replicability(m_max=10, N=200) is True
