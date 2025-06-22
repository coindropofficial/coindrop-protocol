# CoinDrop Protocol 🪂

A sophisticated multi-token airdrop protocol built on Solana using Anchor framework, featuring bonding curve distribution mechanisms and advanced token economics.

## Features

### Core Functionality
- **Multi-Token Support**: Works with any SPL token including Token2022 extensions
- **Bonding Curve Distribution**: Dynamic token distribution using configurable bonding curves
- **Exponential Decay**: Optional exponential decay for purchase amounts to create varied distribution patterns
- **Webapp Authority**: Secure authorization system requiring webapp signatures for claims
- **Unique Wallet Enforcement**: Optional requirement for unique wallet addresses per airdrop

### Advanced Features
- **Flexible Expiration**: Time-based airdrop expiration with automatic token return
- **Recharge Capability**: Add additional tokens to existing airdrops
- **Close Authority Management**: Revocable close authority for enhanced security
- **Transfer Fee Support**: Full compatibility with Token2022 transfer fees
- **Event Emission**: Comprehensive event logging for all operations

## Architecture

### Program Structure

The protocol consists of several key components:

1. **AirdropAccount**: Stores airdrop configuration and state
2. **ClaimRecord**: Tracks individual recipient claims
3. **Bonding Curve Engine**: Calculates distribution amounts dynamically
4. **Authority System**: Multi-level authorization for operations

### Key Instructions

- `create_airdrop`: Initialize a new airdrop with specified parameters
- `distribute_airdrop`: Claim tokens using bonding curve calculation
- `expire_airdrop`: Handle expired airdrops and return remaining tokens
- `close_airdrop`: Manually close an airdrop (if authority not revoked)
- `revoke_close_authority`: Permanently disable manual closing
- `recharge_airdrop`: Add more tokens to an existing airdrop

## Getting Started

### Prerequisites

- [Rust](https://rustup.rs/) (latest stable)
- [Solana CLI](https://docs.solana.com/cli/install-solana-cli-tools)
- [Anchor Framework](https://book.anchor-lang.com/getting_started/installation.html)

### Installation

1. Clone the repository:
```bash
git clone <repository-url>
cd coindrop-protocol
```

2. Build the program:
```bash
anchor build
```

3. Deploy to your desired network:
```bash
anchor deploy
```

## Usage

### Creating an Airdrop

```rust
// Example parameters for creating an airdrop
let airdrop_params = CreateAirdropParams {
    airdrop_id: 1,
    total_supply: 1_000_000 * 10^decimals, // 1M tokens
    expiration_time: 7 * 24 * 60 * 60, // 7 days in seconds
    k_value: 1000, // Bonding curve parameter
    require_unique_wallets: true,
    use_exponential_decay: false,
    revoke_close_authority: false,
};
```

### Claiming Tokens

Users can claim tokens through the `distribute_airdrop` instruction. The amount received is calculated using the bonding curve formula based on:
- Current virtual SOL reserves
- Total token supply
- K-value (curve steepness)
- Purchase amount (simulated)

### Bonding Curve Formula

The distribution amount is calculated using:
```
dy = (y * dx) / (x + dx)
```

Where:
- `dy` = tokens to distribute
- `y` = remaining token supply
- `dx` = purchase amount (in lamports)
- `x` = current virtual SOL reserves

## Configuration

### Airdrop Parameters

| Parameter | Description | Type |
|-----------|-------------|------|
| `airdrop_id` | Unique identifier for the airdrop | `u64` |
| `total_supply` | Total tokens available for distribution | `u64` |
| `expiration_time` | Duration before airdrop expires (seconds) | `u64` |
| `k_value` | Bonding curve steepness parameter | `u64` |
| `require_unique_wallets` | Enforce one claim per wallet | `bool` |
| `use_exponential_decay` | Enable variable purchase amounts | `bool` |
| `revoke_close_authority` | Disable manual closing permanently | `bool` |

### Environment Variables

Set the program ID in `lib.rs`:
```rust
declare_id!("YOUR_PROGRAM_ID_HERE");
```

## Security Features

- **PDA-based Security**: All accounts use Program Derived Addresses
- **Authority Validation**: Multi-level authority checks
- **Overflow Protection**: Safe arithmetic operations throughout
- **Expiration Enforcement**: Automatic expiration handling
- **Transfer Fee Compatibility**: Handles Token2022 transfer fees correctly

## Testing

Run the test suite:
```bash
anchor test
```

For local development:
```bash
solana-test-validator
anchor test --skip-local-validator
```

## Events

The protocol emits the following events:

- `AirdropCreated`: When a new airdrop is initialized
- `TokensDistributed`: When tokens are claimed
- `AirdropClosed`: When an airdrop is manually closed
- `AirdropExpired`: When an airdrop expires
- `CloseAuthorityRevoked`: When close authority is revoked
- `AirdropRecharged`: When tokens are added to an existing airdrop

## Contributing

1. Fork the repository
2. Create a feature branch
3. Make your changes
4. Add tests for new functionality
5. Submit a pull request

## License

[Insert your license here]

## Support

For support and questions:
- Create an issue in this repository
- [Insert additional support channels]

---