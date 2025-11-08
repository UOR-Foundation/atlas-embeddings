import { ethers } from "hardhat";
import * as fs from "fs";
import * as path from "path";

async function main() {
  console.log("Deploying MTPI contract...");

  const [deployer] = await ethers.getSigners();
  console.log("Deploying with account:", deployer.address);

  // Get the contract factory
  const MTPI = await ethers.getContractFactory("MTPI");
  
  // Deploy the contract
  const mtpi = await MTPI.deploy("Atlas MTPI", "1.0.0");
  await mtpi.waitForDeployment();
  
  const address = await mtpi.getAddress();
  console.log("MTPI deployed to:", address);

  // Get network info
  const network = await ethers.provider.getNetwork();
  const networkName = network.name === "unknown" ? "local" : network.name;
  
  console.log("Network:", networkName, "Chain ID:", network.chainId);

  // Prepare deployment info
  const deploymentInfo = {
    network: networkName,
    chainId: Number(network.chainId),
    contractName: "MTPI",
    address: address,
    deployer: deployer.address,
    timestamp: new Date().toISOString(),
    blockNumber: await ethers.provider.getBlockNumber(),
    constructor: {
      name: "Atlas MTPI",
      version: "1.0.0"
    }
  };

  // Save deployment info
  const deploymentsDir = path.join(__dirname, "..", "deployments");
  if (!fs.existsSync(deploymentsDir)) {
    fs.mkdirSync(deploymentsDir, { recursive: true });
  }

  const deploymentFile = path.join(deploymentsDir, `${networkName}.json`);
  fs.writeFileSync(deploymentFile, JSON.stringify(deploymentInfo, null, 2));
  
  console.log(`Deployment info saved to deployments/${networkName}.json`);

  // Verify the deployment
  const name = await mtpi.name();
  const version = await mtpi.version();
  const owner = await mtpi.owner();
  
  console.log("\nDeployment verification:");
  console.log("  Name:", name);
  console.log("  Version:", version);
  console.log("  Owner:", owner);
  console.log("\n✓ Deployment successful!");
}

main()
  .then(() => process.exit(0))
  .catch((error) => {
    console.error(error);
    process.exit(1);
  });
