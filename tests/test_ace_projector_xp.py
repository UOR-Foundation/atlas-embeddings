"""
Tests for ACE projector with XP backend.
"""
import sys

# Avoid local numpy stub by importing directly
import numpy as np_
import pytest
from multiplicity_core.ace_projector_xp import (
    KKTCertificate,
    kkt_residual_l1w,
    project_spectral_ball,
    soft_threshold_l1w,
)


def test_soft_threshold_l1w_zero():
    """Test soft threshold with zero input."""
    y = np_.zeros(10)
    w = np_.ones(10)
    z, cert = soft_threshold_l1w(y, lam=0.1, w=w)
    assert np_.allclose(z, 0.0)
    assert cert.residual < 1e-10
    assert cert.active_frac == 0.0


def test_soft_threshold_l1w_active():
    """Test soft threshold with active components."""
    y = np_.array([0.0, 1.0, -1.0, 0.5])
    w = np_.ones(4)
    lam = 0.3
    z, cert = soft_threshold_l1w(y, lam=lam, w=w)
    
    # Expected: sign(y) * max(|y| - lam*w, 0)
    expected = np_.sign(y) * np_.maximum(np_.abs(y) - lam * w, 0.0)
    assert np_.allclose(z, expected)
    assert cert.residual < 1e-10


def test_soft_threshold_l1w_weighted():
    """Test soft threshold with non-uniform weights."""
    y = np_.array([1.0, 1.0, 1.0, 1.0])
    w = np_.array([0.1, 0.5, 1.0, 2.0])
    lam = 0.5
    z, cert = soft_threshold_l1w(y, lam=lam, w=w)
    
    # Higher weights => more shrinkage
    assert z[0] > z[1] > z[2] > z[3]


def test_kkt_residual_l1w():
    """Test KKT residual computation."""
    y = np_.array([1.0, -1.0, 0.5, -0.5])
    w = np_.ones(4)
    lam = 0.3
    
    # Get optimal z
    z, cert = soft_threshold_l1w(y, lam=lam, w=w)
    
    # Compute KKT residual
    residual = kkt_residual_l1w(y, z, lam, w)
    assert residual < 1e-10


def test_project_spectral_ball_inside():
    """Test spectral projection when already inside ball."""
    K = np_.array([[0.1, 0.0], [0.0, 0.1]])
    radius = 1.0
    K_proj, scale, sigma_max = project_spectral_ball(K, radius)
    
    assert scale == 1.0  # No scaling needed
    assert sigma_max < radius
    assert np_.allclose(K_proj, K)


def test_project_spectral_ball_outside():
    """Test spectral projection when outside ball."""
    K = np_.array([[2.0, 0.0], [0.0, 1.0]])
    radius = 1.0
    K_proj, scale, sigma_max = project_spectral_ball(K, radius)
    
    assert sigma_max > radius
    assert scale < 1.0
    assert np_.allclose(scale, radius / sigma_max)
    
    # Verify projection is on boundary
    s_proj = np_.linalg.svd(K_proj, compute_uv=False)
    assert np_.allclose(s_proj[0], radius, atol=1e-6)


def test_project_spectral_ball_zero_radius():
    """Test spectral projection with zero radius."""
    K = np_.array([[1.0, 0.0], [0.0, 1.0]])
    radius = 0.0
    K_proj, scale, sigma_max = project_spectral_ball(K, radius)
    
    assert np_.allclose(K_proj, 0.0)


def test_project_spectral_ball_empty():
    """Test spectral projection with empty matrix."""
    K = np_.array([]).reshape(0, 0)
    radius = 1.0
    K_proj, scale, sigma_max = project_spectral_ball(K, radius)
    
    assert K_proj.size == 0
    assert scale == 1.0
    assert sigma_max == 0.0


def test_kkt_certificate_structure():
    """Test KKT certificate has expected fields."""
    y = np_.ones(5)
    w = np_.ones(5)
    z, cert = soft_threshold_l1w(y, lam=0.1, w=w)
    
    assert isinstance(cert, KKTCertificate)
    assert hasattr(cert, "residual")
    assert hasattr(cert, "max_stationarity")
    assert hasattr(cert, "max_comp_slack")
    assert hasattr(cert, "active_frac")
    assert 0.0 <= cert.active_frac <= 1.0
