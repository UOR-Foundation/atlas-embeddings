#!/usr/bin/env node
const solc = require('solc');
const fs = require('fs');
const path = require('path');

// Read the contract file
const contractPath = path.join(__dirname, '..', 'contracts', 'MTPI.sol');
const source = fs.readFileSync(contractPath, 'utf8');

// Prepare the input for the compiler
const input = {
  language: 'Solidity',
  sources: {
    'MTPI.sol': {
      content: source
    }
  },
  settings: {
    optimizer: {
      enabled: true,
      runs: 200
    },
    outputSelection: {
      '*': {
        '*': ['abi', 'evm.bytecode', 'evm.deployedBytecode']
      }
    }
  }
};

console.log('Compiling MTPI.sol with Solidity 0.8.27...');

// Compile the contract
const output = JSON.parse(solc.compile(JSON.stringify(input)));

// Check for errors
if (output.errors) {
  let hasError = false;
  output.errors.forEach(error => {
    if (error.severity === 'error') {
      console.error('Error:', error.formattedMessage);
      hasError = true;
    } else {
      console.warn('Warning:', error.formattedMessage);
    }
  });
  if (hasError) {
    process.exit(1);
  }
}

// Extract the compiled contract
const contract = output.contracts['MTPI.sol']['MTPI'];

// Create artifacts directory structure
const artifactsDir = path.join(__dirname, '..', 'artifacts', 'contracts', 'MTPI.sol');
fs.mkdirSync(artifactsDir, { recursive: true });

// Create ABI directory
const abiDir = path.join(__dirname, '..', 'src', 'abi');
fs.mkdirSync(abiDir, { recursive: true });

// Save the full artifact
const artifact = {
  _format: 'hh-sol-artifact-1',
  contractName: 'MTPI',
  sourceName: 'contracts/MTPI.sol',
  abi: contract.abi,
  bytecode: contract.evm.bytecode.object,
  deployedBytecode: contract.evm.deployedBytecode.object,
  linkReferences: {},
  deployedLinkReferences: {}
};

fs.writeFileSync(
  path.join(artifactsDir, 'MTPI.json'),
  JSON.stringify(artifact, null, 2)
);

// Save just the ABI
fs.writeFileSync(
  path.join(abiDir, 'MTPI.json'),
  JSON.stringify(contract.abi, null, 2)
);

console.log('✓ Contract compiled successfully');
console.log('✓ Artifact saved to artifacts/contracts/MTPI.sol/MTPI.json');
console.log('✓ ABI exported to src/abi/MTPI.json');
