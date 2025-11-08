// SPDX-License-Identifier: MIT
pragma solidity 0.8.27;

/**
 * @title MTPI
 * @dev Multi-Type Parameter Interface contract for Atlas Hologram
 */
contract MTPI {
    string public name;
    string public version;
    address public owner;
    
    mapping(bytes32 => bytes) private parameters;
    
    event ParameterSet(bytes32 indexed key, bytes value);
    event OwnershipTransferred(address indexed previousOwner, address indexed newOwner);
    
    modifier onlyOwner() {
        require(msg.sender == owner, "MTPI: caller is not the owner");
        _;
    }
    
    constructor(string memory _name, string memory _version) {
        name = _name;
        version = _version;
        owner = msg.sender;
    }
    
    /**
     * @dev Set a parameter by key
     * @param key The parameter key
     * @param value The parameter value
     */
    function setParameter(bytes32 key, bytes calldata value) external onlyOwner {
        parameters[key] = value;
        emit ParameterSet(key, value);
    }
    
    /**
     * @dev Get a parameter by key
     * @param key The parameter key
     * @return The parameter value
     */
    function getParameter(bytes32 key) external view returns (bytes memory) {
        return parameters[key];
    }
    
    /**
     * @dev Transfer ownership
     * @param newOwner The new owner address
     */
    function transferOwnership(address newOwner) external onlyOwner {
        require(newOwner != address(0), "MTPI: new owner is the zero address");
        address oldOwner = owner;
        owner = newOwner;
        emit OwnershipTransferred(oldOwner, newOwner);
    }
}
