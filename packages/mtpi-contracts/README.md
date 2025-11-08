# MTPI Smart Contracts

MTPI (Multi-Type Parameter Interface) Smart Contracts for Atlas Hologram.

## Overview

This package contains the Solidity smart contracts for MTPI, compiled with Hardhat using Solidity 0.8.27. The contracts are designed to be deployed to both local development networks and Sepolia testnet.

## Project Structure

```
packages/mtpi-contracts/
├── contracts/          # Solidity smart contracts
│   └── MTPI.sol       # Main MTPI contract
├── scripts/           # Deployment and utility scripts
│   ├── compile-manual.js    # Manual compilation script
│   ├── deploy-direct.js     # Direct deployment script
│   └── deploy.ts            # Hardhat deployment script
├── test/              # Test files
│   ├── MTPI.test.ts   # Hardhat unit tests
│   └── MTPI.e2e.ts    # Vitest e2e tests
├── src/abi/           # Exported ABI files (used by consumers)
│   └── MTPI.json
├── deployments/       # Deployment information
│   └── local.json     # Local network deployment
├── artifacts/         # Compiled contract artifacts
└── hardhat.config.ts  # Hardhat configuration
```

## Setup

### Prerequisites

- Node.js >= 18
- npm >= 9

### Installation

```bash
npm install
```

## Usage

### Compile Contracts

Compile the contracts and export ABIs:

```bash
npm run compile
```

This will:
- Compile `contracts/MTPI.sol` using Solidity 0.8.27
- Export the ABI to `src/abi/MTPI.json`
- Generate artifacts in `artifacts/contracts/`

### Deploy to Local Network

Start a local Hardhat node:

```bash
npm run node
```

In another terminal, deploy the contracts:

```bash
npm run deploy:local
```

This will:
- Deploy the MTPI contract to the local network (http://127.0.0.1:8545)
- Save deployment information to `deployments/local.json`

### Deploy to Sepolia

Set environment variables:

```bash
export SEPOLIA_RPC_URL="https://sepolia.infura.io/v3/YOUR-PROJECT-ID"
export PRIVATE_KEY="your-private-key"
```

Deploy:

```bash
npm run deploy:sepolia
```

### Run Tests

#### Unit Tests (Hardhat)

```bash
npm test
```

#### E2E Tests (Vitest)

Ensure the local network is running and contracts are deployed, then:

```bash
npm run test:e2e
```

These tests verify:
- ABI files are correctly exported and accessible
- Deployment information is available
- Contracts can be interacted with using the exported ABIs
- No runtime "missing ABI/address" errors occur

### Clean Build Artifacts

```bash
npm run clean
```

## Configuration

### Solidity Version

The project uses Solidity **0.8.27** as specified in:
- `hardhat.config.ts`: Hardhat configuration
- `scripts/compile-manual.js`: Manual compilation script
- `contracts/MTPI.sol`: Contract pragma

### Networks

#### Local Network
- URL: http://127.0.0.1:8545
- Chain ID: 31337

#### Sepolia Testnet
- URL: Configured via `SEPOLIA_RPC_URL` environment variable
- Chain ID: 11155111
- Requires: `PRIVATE_KEY` environment variable

## Contract Consumers

Applications consuming these contracts should:

1. **Import ABIs** from `packages/mtpi-contracts/src/abi/`
2. **Load deployment info** from `packages/mtpi-contracts/deployments/*.json`

Example:

```typescript
import mtpiAbi from '@atlas-hologram/mtpi-contracts/src/abi/MTPI.json';
import deploymentInfo from '@atlas-hologram/mtpi-contracts/deployments/local.json';

const contract = new ethers.Contract(
  deploymentInfo.address,
  mtpiAbi,
  provider
);
```

## CI/CD

### Smoke Test Pipeline

The recommended CI smoke test workflow:

1. Install dependencies
2. Compile contracts
3. Start Anvil (or Hardhat node)
4. Deploy contracts to local network
5. Run e2e tests

Example:

```bash
npm install
npm run compile
npm run node &  # Start in background
sleep 5
npm run deploy:local
npm run test:e2e
```

## Outputs

### ABIs

ABI files are exported to `src/abi/` for consumption by applications:
- `src/abi/MTPI.json`

### Deployment Information

Deployment information is saved to `deployments/` per network:
- `deployments/local.json`
- `deployments/sepolia.json`

Each file contains:
- `network`: Network name
- `chainId`: Chain ID
- `contractName`: Contract name
- `address`: Deployed contract address
- `deployer`: Deployer address
- `timestamp`: Deployment timestamp
- `blockNumber`: Block number at deployment
- `constructor`: Constructor arguments

## License

MIT
