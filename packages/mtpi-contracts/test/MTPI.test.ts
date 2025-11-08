import { expect } from "chai";
import { ethers } from "hardhat";
import { MTPI } from "../typechain-types";

describe("MTPI", function () {
  let mtpi: MTPI;
  let owner: any;
  let addr1: any;

  beforeEach(async function () {
    [owner, addr1] = await ethers.getSigners();
    const MTPI = await ethers.getContractFactory("MTPI");
    mtpi = await MTPI.deploy("Test MTPI", "1.0.0");
    await mtpi.waitForDeployment();
  });

  describe("Deployment", function () {
    it("Should set the right name and version", async function () {
      expect(await mtpi.name()).to.equal("Test MTPI");
      expect(await mtpi.version()).to.equal("1.0.0");
    });

    it("Should set the right owner", async function () {
      expect(await mtpi.owner()).to.equal(owner.address);
    });
  });

  describe("Parameters", function () {
    it("Should set and get a parameter", async function () {
      const key = ethers.id("test.key");
      const value = ethers.toUtf8Bytes("test value");
      
      await mtpi.setParameter(key, value);
      const retrieved = await mtpi.getParameter(key);
      
      expect(ethers.toUtf8String(retrieved)).to.equal("test value");
    });

    it("Should only allow owner to set parameters", async function () {
      const key = ethers.id("test.key");
      const value = ethers.toUtf8Bytes("test value");
      
      await expect(
        mtpi.connect(addr1).setParameter(key, value)
      ).to.be.revertedWith("MTPI: caller is not the owner");
    });

    it("Should emit ParameterSet event", async function () {
      const key = ethers.id("test.key");
      const value = ethers.toUtf8Bytes("test value");
      
      await expect(mtpi.setParameter(key, value))
        .to.emit(mtpi, "ParameterSet")
        .withArgs(key, value);
    });
  });

  describe("Ownership", function () {
    it("Should transfer ownership", async function () {
      await mtpi.transferOwnership(addr1.address);
      expect(await mtpi.owner()).to.equal(addr1.address);
    });

    it("Should only allow owner to transfer ownership", async function () {
      await expect(
        mtpi.connect(addr1).transferOwnership(addr1.address)
      ).to.be.revertedWith("MTPI: caller is not the owner");
    });

    it("Should not allow transfer to zero address", async function () {
      await expect(
        mtpi.transferOwnership(ethers.ZeroAddress)
      ).to.be.revertedWith("MTPI: new owner is the zero address");
    });

    it("Should emit OwnershipTransferred event", async function () {
      await expect(mtpi.transferOwnership(addr1.address))
        .to.emit(mtpi, "OwnershipTransferred")
        .withArgs(owner.address, addr1.address);
    });
  });
});
