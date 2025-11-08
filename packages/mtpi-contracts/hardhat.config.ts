import { HardhatUserConfig } from "hardhat/config";
import "@nomicfoundation/hardhat-toolbox";
import * as fs from "fs";
import * as path from "path";

const config: HardhatUserConfig = {
  solidity: {
    compilers: [
      {
        version: "0.8.27",
        settings: {
          optimizer: {
            enabled: true,
            runs: 200,
          },
          viaIR: false,
        },
      },
    ],
  },
  networks: {
    local: {
      url: "http://127.0.0.1:8545",
      chainId: 31337,
    },
    sepolia: {
      url: process.env.SEPOLIA_RPC_URL || "https://sepolia.infura.io/v3/YOUR-PROJECT-ID",
      accounts: process.env.PRIVATE_KEY ? [process.env.PRIVATE_KEY] : [],
      chainId: 11155111,
    },
  },
  paths: {
    sources: "./contracts",
    tests: "./test",
    cache: "./cache",
    artifacts: "./artifacts",
  },
};

// Custom task to export ABIs after compilation
import { task } from "hardhat/config";

task("compile", "Compiles the entire project, building all artifacts")
  .setAction(async (taskArgs, hre, runSuper) => {
    await runSuper(taskArgs);
    
    // Export ABIs to src/abi directory
    const artifactsPath = path.join(__dirname, "artifacts", "contracts");
    const abiPath = path.join(__dirname, "src", "abi");
    
    // Ensure abi directory exists
    if (!fs.existsSync(abiPath)) {
      fs.mkdirSync(abiPath, { recursive: true });
    }
    
    // Process all contract artifacts
    if (fs.existsSync(artifactsPath)) {
      processDirectory(artifactsPath, abiPath);
    }
    
    console.log("✓ ABIs exported to src/abi/");
  });

function processDirectory(dir: string, outputDir: string) {
  const entries = fs.readdirSync(dir, { withFileTypes: true });
  
  for (const entry of entries) {
    const fullPath = path.join(dir, entry.name);
    
    if (entry.isDirectory()) {
      processDirectory(fullPath, outputDir);
    } else if (entry.name.endsWith(".json") && !entry.name.endsWith(".dbg.json")) {
      const artifact = JSON.parse(fs.readFileSync(fullPath, "utf8"));
      if (artifact.abi && artifact.abi.length > 0) {
        const contractName = path.basename(entry.name, ".json");
        const abiFile = path.join(outputDir, `${contractName}.json`);
        fs.writeFileSync(abiFile, JSON.stringify(artifact.abi, null, 2));
      }
    }
  }
}

export default config;
