#!/usr/bin/env node
const { ethers } = require('ethers');
const fs = require('fs');
const path = require('path');

async function main() {
  console.log('Deploying MTPI contract...');

  // Read the compiled artifact
  const artifactPath = path.join(__dirname, '..', 'artifacts', 'contracts', 'MTPI.sol', 'MTPI.json');
  const artifact = JSON.parse(fs.readFileSync(artifactPath, 'utf8'));

  // Connect to local network
  const networkUrl = process.env.NETWORK_URL || 'http://127.0.0.1:8545';
  const provider = new ethers.JsonRpcProvider(networkUrl);
  
  // Get signer (use first account from Hardhat node)
  const signer = await provider.getSigner(0);
  const deployerAddress = await signer.getAddress();
  
  console.log('Deploying with account:', deployerAddress);
  
  // Create contract factory
  const factory = new ethers.ContractFactory(artifact.abi, artifact.bytecode, signer);
  
  // Deploy the contract
  const contract = await factory.deploy('Atlas MTPI', '1.0.0');
  await contract.waitForDeployment();
  
  const address = await contract.getAddress();
  console.log('MTPI deployed to:', address);

  // Get network info
  const network = await provider.getNetwork();
  const networkName = process.env.NETWORK_NAME || 'local';
  
  console.log('Network:', networkName, 'Chain ID:', network.chainId.toString());

  // Prepare deployment info
  const deploymentInfo = {
    network: networkName,
    chainId: Number(network.chainId),
    contractName: 'MTPI',
    address: address,
    deployer: deployerAddress,
    timestamp: new Date().toISOString(),
    blockNumber: await provider.getBlockNumber(),
    constructor: {
      name: 'Atlas MTPI',
      version: '1.0.0'
    }
  };

  // Save deployment info
  const deploymentsDir = path.join(__dirname, '..', 'deployments');
  if (!fs.existsSync(deploymentsDir)) {
    fs.mkdirSync(deploymentsDir, { recursive: true });
  }

  const deploymentFile = path.join(deploymentsDir, `${networkName}.json`);
  fs.writeFileSync(deploymentFile, JSON.stringify(deploymentInfo, null, 2));
  
  console.log(`Deployment info saved to deployments/${networkName}.json`);

  // Verify the deployment
  const name = await contract.name();
  const version = await contract.version();
  const owner = await contract.owner();
  
  console.log('\nDeployment verification:');
  console.log('  Name:', name);
  console.log('  Version:', version);
  console.log('  Owner:', owner);
  console.log('\n✓ Deployment successful!');
}

main()
  .then(() => process.exit(0))
  .catch((error) => {
    console.error(error);
    process.exit(1);
  });
