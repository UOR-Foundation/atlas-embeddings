import { describe, it, expect, beforeAll } from 'vitest';
import { ethers } from 'ethers';
import * as fs from 'fs';
import * as path from 'path';

// Import ABI from src/abi directory
import mtpiAbi from '../src/abi/MTPI.json';

describe('MTPI Contract E2E Tests', () => {
  let provider: ethers.JsonRpcProvider;
  let signer: ethers.Signer;
  let contract: ethers.Contract;
  let deploymentInfo: any;

  beforeAll(async () => {
    // Load deployment info
    const deploymentPath = path.join(__dirname, '..', 'deployments', 'local.json');
    if (!fs.existsSync(deploymentPath)) {
      throw new Error('Deployment file not found. Run deployment first.');
    }
    deploymentInfo = JSON.parse(fs.readFileSync(deploymentPath, 'utf8'));

    // Connect to local network
    provider = new ethers.JsonRpcProvider('http://127.0.0.1:8545');
    signer = await provider.getSigner(0);

    // Create contract instance using ABI from src/abi
    contract = new ethers.Contract(deploymentInfo.address, mtpiAbi, signer);
  });

  describe('ABI Loading', () => {
    it('should successfully load ABI from src/abi directory', () => {
      expect(mtpiAbi).toBeDefined();
      expect(Array.isArray(mtpiAbi)).toBe(true);
      expect(mtpiAbi.length).toBeGreaterThan(0);
    });

    it('should have expected ABI methods', () => {
      const functionNames = mtpiAbi
        .filter((item: any) => item.type === 'function')
        .map((item: any) => item.name);
      
      expect(functionNames).toContain('name');
      expect(functionNames).toContain('version');
      expect(functionNames).toContain('owner');
      expect(functionNames).toContain('setParameter');
      expect(functionNames).toContain('getParameter');
      expect(functionNames).toContain('transferOwnership');
    });
  });

  describe('Deployment Info', () => {
    it('should have valid deployment info', () => {
      expect(deploymentInfo.address).toBeDefined();
      expect(deploymentInfo.network).toBe('local');
      expect(deploymentInfo.chainId).toBe(31337);
      expect(deploymentInfo.contractName).toBe('MTPI');
    });

    it('should have contract deployed at specified address', async () => {
      const code = await provider.getCode(deploymentInfo.address);
      expect(code).not.toBe('0x');
      expect(code.length).toBeGreaterThan(2);
    });
  });

  describe('Contract Interaction', () => {
    it('should read contract name and version', async () => {
      const name = await contract.name();
      const version = await contract.version();
      
      expect(name).toBe('Atlas MTPI');
      expect(version).toBe('1.0.0');
    });

    it('should read contract owner', async () => {
      const owner = await contract.owner();
      expect(owner).toBe(deploymentInfo.deployer);
    });

    it('should set and get parameters', async () => {
      const key = ethers.id('test.parameter');
      const value = ethers.toUtf8Bytes('test value');
      
      const tx = await contract.setParameter(key, value);
      await tx.wait();
      
      const retrieved = await contract.getParameter(key);
      const retrievedString = ethers.toUtf8String(retrieved);
      
      expect(retrievedString).toBe('test value');
    });

    it('should emit ParameterSet event', async () => {
      const key = ethers.id('test.event');
      const value = ethers.toUtf8Bytes('event value');
      
      const tx = await contract.setParameter(key, value);
      const receipt = await tx.wait();
      
      // Check that ParameterSet event was emitted
      const event = receipt.logs.find((log: any) => {
        try {
          const parsed = contract.interface.parseLog(log);
          return parsed?.name === 'ParameterSet';
        } catch {
          return false;
        }
      });
      
      expect(event).toBeDefined();
    });

    it('should not allow non-owner to set parameters', async () => {
      const key = ethers.id('test.unauthorized');
      const value = ethers.toUtf8Bytes('unauthorized');
      
      // Get a different signer (non-owner)
      const otherSigner = await provider.getSigner(1);
      const contractAsOther = contract.connect(otherSigner);
      
      await expect(
        contractAsOther.setParameter(key, value)
      ).rejects.toThrow();
    });
  });

  describe('No Missing ABI/Address Errors', () => {
    it('should not have runtime missing ABI errors', () => {
      expect(() => {
        // Test that we can access ABI without errors
        const iface = new ethers.Interface(mtpiAbi);
        expect(iface).toBeDefined();
      }).not.toThrow();
    });

    it('should not have missing address errors', () => {
      expect(deploymentInfo.address).toBeDefined();
      expect(ethers.isAddress(deploymentInfo.address)).toBe(true);
    });

    it('should successfully create contract instance', () => {
      expect(() => {
        const testContract = new ethers.Contract(
          deploymentInfo.address,
          mtpiAbi,
          provider
        );
        expect(testContract).toBeDefined();
      }).not.toThrow();
    });
  });
});
