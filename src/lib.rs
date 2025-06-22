use anchor_spl::token_interface::{self, Mint, TokenAccount, TokenInterface, TransferChecked};
use anchor_lang::prelude::*;

declare_id!("new_program_id_tbd"); // new program id not set yet

#[program]
pub mod airdrop_protocol {
    use super::*;

    /// Creates a new airdrop with the specified parameters
    pub fn create_airdrop(
        ctx: Context<CreateAirdrop>,
        airdrop_id: u64,
        total_supply: u64,
        expiration_time: u64,
        k_value: u64,
        require_unique_wallets: bool,
        use_exponential_decay: bool,
        revoke_close_authority: bool,
    ) -> Result<()> {
        let airdrop = &mut ctx.accounts.airdrop;
        let creator = &ctx.accounts.creator;
        let mint = &ctx.accounts.mint;
        let clock = Clock::get()?;

        // Validate parameters
        require!(total_supply > 0, AirdropError::InvalidTotalSupply);
        require!(k_value > 0, AirdropError::InvalidKValue);
        require!(expiration_time > 0, AirdropError::InvalidExpirationTime);

        // Initialize airdrop account
        airdrop.airdrop_id = airdrop_id;
        airdrop.creator = creator.key();
        airdrop.mint = mint.key();
        airdrop.webapp_authority = ctx.accounts.webapp_authority.key();
        airdrop.total_supply = total_supply;
        airdrop.remaining_supply = total_supply;
        airdrop.claims_made = 0;
        airdrop.is_closed = false;
        airdrop.close_authority_revoked = revoke_close_authority;
        airdrop.created_at = clock.unix_timestamp as u64;
        airdrop.expiration_time = expiration_time;
        airdrop.k_value = k_value;
        airdrop.require_unique_wallets = require_unique_wallets;
        airdrop.virtual_sol_reserves = 0;
        airdrop.bump = ctx.bumps.airdrop;
        airdrop.use_exponential_decay = use_exponential_decay;

        // Transfer tokens from creator to airdrop vault
        let transfer_ctx = CpiContext::new(
            ctx.accounts.token_program.to_account_info(),
            TransferChecked {
                from: ctx.accounts.creator_token_account.to_account_info(),
                to: ctx.accounts.airdrop_vault.to_account_info(),
                authority: creator.to_account_info(),
                mint: ctx.accounts.mint.to_account_info(),
            },
        );
        token_interface::transfer_checked(transfer_ctx, total_supply, ctx.accounts.mint.decimals)?;

        emit!(AirdropCreated {
            airdrop: airdrop.key(),
            creator: creator.key(),
            mint: mint.key(),
            airdrop_id,
            total_supply,
            expiration_time,
            k_value,
            require_unique_wallets,
            use_exponential_decay,
            revoke_close_authority,
        });

        Ok(())
    }

    /// Distributes tokens to a recipient using the bonding curve
    pub fn distribute_airdrop(ctx: Context<DistributeAirdrop>) -> Result<()> {
        let airdrop = &mut ctx.accounts.airdrop;
        let recipient = &ctx.accounts.recipient;
        let claim_record = &mut ctx.accounts.claim_record;
        let clock = Clock::get()?;

        // Check webapp authority
        require!(
            airdrop.webapp_authority == ctx.accounts.webapp_authority.key(),
            AirdropError::UnauthorizedClaim
        );

        // Check expiration
        let current_time = clock.unix_timestamp as u64;
        require!(
            current_time < airdrop.created_at + airdrop.expiration_time,
            AirdropError::AirdropExpired
        );

        // Ensure airdrop is still active
        require!(!airdrop.is_closed, AirdropError::AirdropClosed);

        // Check unique wallet requirement
        if airdrop.require_unique_wallets {
            require!(!claim_record.has_claimed, AirdropError::AlreadyClaimed);
        }

        // Calculate distribution amount using bonding curve with purchase amount
        let base_purchase_amount = if airdrop.use_exponential_decay {
            generate_exponential_decay_random(airdrop.claims_made, recipient.key())?
        } else {
            1_000_000_000 // Standard 1 SOL (in lamports) purchase for each claim
        };
        // Divide the entire purchase amount by 10 to get 0.1x effect
        let purchase_amount = base_purchase_amount.saturating_div(10);
        let distribution_amount = calculate_distribution_amount(
            airdrop.virtual_sol_reserves,
            airdrop.total_supply,
            airdrop.k_value,
            purchase_amount,
        )?;

        // For Token2022 with transfer fees, the actual vault balance might be less than remaining_supply
        // Get the actual vault balance and use the smaller of distribution_amount or actual balance
        let actual_vault_balance = ctx.accounts.airdrop_vault.amount;
        
        // Ensure there are enough tokens remaining (use the minimum of logical and actual)
        let effective_remaining = std::cmp::min(airdrop.remaining_supply, actual_vault_balance);
        require!(
            distribution_amount <= effective_remaining,
            AirdropError::InsufficientTokens
        );

        // Cap distribution amount to what's actually available in the vault
        let actual_distribution_amount = std::cmp::min(distribution_amount, actual_vault_balance);

        // Update airdrop state - use actual distribution amount
        airdrop.remaining_supply = airdrop.remaining_supply.saturating_sub(actual_distribution_amount);
        airdrop.claims_made = airdrop.claims_made.saturating_add(1);
        airdrop.virtual_sol_reserves = airdrop.virtual_sol_reserves.saturating_add(purchase_amount);

        // Update claim record
        if airdrop.require_unique_wallets {
            claim_record.recipient = recipient.key();
            claim_record.airdrop = airdrop.key();
            claim_record.amount_claimed = actual_distribution_amount;
            claim_record.has_claimed = true;
            claim_record.bump = ctx.bumps.claim_record;
        } else {
            // For non-unique wallets, we still track the claim but allow multiple
            claim_record.recipient = recipient.key();
            claim_record.airdrop = airdrop.key();
            claim_record.amount_claimed = claim_record.amount_claimed.saturating_add(actual_distribution_amount);
            claim_record.has_claimed = true;
            claim_record.bump = ctx.bumps.claim_record;
        }

        // Transfer tokens from airdrop vault to recipient
        let seeds = &[
            b"airdrop",
            airdrop.creator.as_ref(),
            airdrop.mint.as_ref(),
            &airdrop.airdrop_id.to_le_bytes(),
            &[airdrop.bump],
        ];
        let signer = &[&seeds[..]];

        let transfer_ctx = CpiContext::new_with_signer(
            ctx.accounts.token_program.to_account_info(),
            TransferChecked {
                from: ctx.accounts.airdrop_vault.to_account_info(),
                to: ctx.accounts.recipient_token_account.to_account_info(),
                authority: airdrop.to_account_info(),
                mint: ctx.accounts.mint.to_account_info(),
            },
            signer,
        );
        token_interface::transfer_checked(transfer_ctx, actual_distribution_amount, ctx.accounts.mint.decimals)?;

        emit!(TokensDistributed {
            airdrop: airdrop.key(),
            recipient: recipient.key(),
            amount: actual_distribution_amount,
            claims_made: airdrop.claims_made,
        });

        Ok(())
    }

    /// Expires an airdrop and returns remaining tokens to creator
    pub fn expire_airdrop(ctx: Context<ExpireAirdrop>) -> Result<()> {
        let airdrop = &mut ctx.accounts.airdrop;
        let clock = Clock::get()?;

        // Check if airdrop has actually expired
        let current_time = clock.unix_timestamp as u64;
        require!(
            current_time >= airdrop.created_at + airdrop.expiration_time,
            AirdropError::AirdropNotExpired
        );

        // Ensure airdrop isn't already closed
        require!(!airdrop.is_closed, AirdropError::AirdropClosed);

        // Get the actual vault balance instead of using remaining_supply
        // This handles Token2022 transfer fees that may have reduced the vault balance
        let actual_vault_balance = ctx.accounts.airdrop_vault.amount;
        let tokens_returned = actual_vault_balance;

        // Transfer actual vault balance back to creator (if any)
        if actual_vault_balance > 0 {
            let seeds = &[
                b"airdrop",
                airdrop.creator.as_ref(),
                airdrop.mint.as_ref(),
                &airdrop.airdrop_id.to_le_bytes(),
                &[airdrop.bump],
            ];
            let signer = &[&seeds[..]];

            let transfer_ctx = CpiContext::new_with_signer(
                ctx.accounts.token_program.to_account_info(),
                TransferChecked {
                    from: ctx.accounts.airdrop_vault.to_account_info(),
                    to: ctx.accounts.creator_token_account.to_account_info(),
                    authority: airdrop.to_account_info(),
                    mint: ctx.accounts.mint.to_account_info(),
                },
                signer,
            );
            token_interface::transfer_checked(transfer_ctx, actual_vault_balance, ctx.accounts.mint.decimals)?;
        }

        // Mark as closed and reset remaining supply to match actual state
        airdrop.is_closed = true;
        airdrop.remaining_supply = 0;

        emit!(AirdropExpired {
            airdrop: airdrop.key(),
            creator: airdrop.creator,
            tokens_returned,
        });

        Ok(())
    }

    /// Closes the airdrop and returns remaining tokens to creator
    pub fn close_airdrop(ctx: Context<CloseAirdrop>) -> Result<()> {
        let airdrop = &mut ctx.accounts.airdrop;
        let creator = &ctx.accounts.creator;

        // Ensure only creator can close
        require!(airdrop.creator == creator.key(), AirdropError::UnauthorizedClose);

        // Ensure close authority hasn't been revoked
        require!(!airdrop.close_authority_revoked, AirdropError::CloseAuthorityRevoked);

        // Ensure airdrop isn't already closed
        require!(!airdrop.is_closed, AirdropError::AirdropClosed);

        // Get the actual vault balance instead of using remaining_supply
        // This handles Token2022 transfer fees that may have reduced the vault balance
        let actual_vault_balance = ctx.accounts.airdrop_vault.amount;
        let tokens_returned = actual_vault_balance;

        // Transfer actual vault balance back to creator (if any)
        if actual_vault_balance > 0 {
            let seeds = &[
                b"airdrop",
                airdrop.creator.as_ref(),
                airdrop.mint.as_ref(),
                &airdrop.airdrop_id.to_le_bytes(),
                &[airdrop.bump],
            ];
            let signer = &[&seeds[..]];

            let transfer_ctx = CpiContext::new_with_signer(
                ctx.accounts.token_program.to_account_info(),
                TransferChecked {
                    from: ctx.accounts.airdrop_vault.to_account_info(),
                    to: ctx.accounts.creator_token_account.to_account_info(),
                    authority: airdrop.to_account_info(),
                    mint: ctx.accounts.mint.to_account_info(),
                },
                signer,
            );
            token_interface::transfer_checked(transfer_ctx, actual_vault_balance, ctx.accounts.mint.decimals)?;
        }

        // Mark as closed and reset remaining supply to match actual state
        airdrop.is_closed = true;
        airdrop.remaining_supply = 0;

        emit!(AirdropClosed {
            airdrop: airdrop.key(),
            creator: creator.key(),
            tokens_returned,
        });

        Ok(())
    }

    /// Revokes the ability to close the airdrop
    pub fn revoke_close_authority(ctx: Context<RevokeCloseAuthority>) -> Result<()> {
        let airdrop = &mut ctx.accounts.airdrop;
        let creator = &ctx.accounts.creator;

        // Ensure only creator can revoke
        require!(airdrop.creator == creator.key(), AirdropError::UnauthorizedRevoke);

        // Ensure close authority hasn't already been revoked
        require!(!airdrop.close_authority_revoked, AirdropError::CloseAuthorityRevoked);

        airdrop.close_authority_revoked = true;

        emit!(CloseAuthorityRevoked {
            airdrop: airdrop.key(),
            creator: creator.key(),
        });

        Ok(())
    }

    /// Recharges an airdrop with additional tokens and recalculates virtual SOL reserves
    /// Anyone can recharge an airdrop by providing tokens
    pub fn recharge_airdrop(
        ctx: Context<RechargeAirdrop>,
        additional_tokens: u64,
    ) -> Result<()> {
        let airdrop = &mut ctx.accounts.airdrop;
        let recharger = &ctx.accounts.recharger;

        // Ensure airdrop isn't closed
        require!(!airdrop.is_closed, AirdropError::AirdropClosed);

        // Validate additional tokens
        require!(additional_tokens > 0, AirdropError::InvalidRechargeAmount);

        // Get the current actual vault balance before adding new tokens
        let current_vault_balance = ctx.accounts.airdrop_vault.amount;
        
        // Calculate actual distributed tokens based on vault balance vs logical remaining supply
        // If vault balance is less than remaining supply, it means fees were deducted
        let actual_remaining_supply = std::cmp::min(airdrop.remaining_supply, current_vault_balance);
        let distributed_tokens = airdrop.total_supply.saturating_sub(actual_remaining_supply);

        // Transfer additional tokens from recharger to airdrop vault first
        let transfer_ctx = CpiContext::new(
            ctx.accounts.token_program.to_account_info(),
            TransferChecked {
                from: ctx.accounts.recharger_token_account.to_account_info(),
                to: ctx.accounts.airdrop_vault.to_account_info(),
                authority: recharger.to_account_info(),
                mint: ctx.accounts.mint.to_account_info(),
            },
        );
        token_interface::transfer_checked(transfer_ctx, additional_tokens, ctx.accounts.mint.decimals)?;

        // Get the vault balance after the transfer (may be less than expected due to fees)
        ctx.accounts.airdrop_vault.reload()?;
        let new_vault_balance = ctx.accounts.airdrop_vault.amount;
        let actual_tokens_added = new_vault_balance.saturating_sub(current_vault_balance);

        // Calculate new total supply based on actual tokens received
        let new_total_supply = airdrop.total_supply.saturating_add(actual_tokens_added);

        // Calculate new remaining supply (maintaining same distributed amount)
        let new_remaining_supply = new_total_supply.saturating_sub(distributed_tokens);

        // Recalculate virtual SOL reserves to maintain the bonding curve state
        // Formula: remaining = k * total / (k + virtual_reserves)
        // Solving for virtual_reserves: virtual_reserves = (k * total / remaining) - k
        // Convert k_value to lamports for calculations
        let k_value_lamports = airdrop.k_value.saturating_mul(1_000_000_000);
        let new_virtual_sol_reserves = if new_remaining_supply > 0 {
            let numerator : u128 = (k_value_lamports as u128).saturating_mul(new_total_supply as u128);
            let quotient : u128 = numerator.saturating_div(new_remaining_supply as u128);
            (quotient.saturating_sub(k_value_lamports as u128) as u64)
        } else {
            // If no tokens remain, set virtual reserves to a high value to prevent further distribution
            u64::MAX / 2 // Use a large but safe value
        };

        // Update airdrop state with actual values
        airdrop.total_supply = new_total_supply;
        airdrop.remaining_supply = new_remaining_supply;
        airdrop.virtual_sol_reserves = new_virtual_sol_reserves;

        emit!(AirdropRecharged {
            airdrop: airdrop.key(),
            recharger: recharger.key(),
            additional_tokens: actual_tokens_added, // Emit actual tokens added, not requested
            new_total_supply,
            new_virtual_sol_reserves,
        });

        Ok(())
    }
}

/// Generates a random number from 1 to 20 SOL (in lamports) using exponential decay probability
/// Uses the seed from claims_made and recipient key to ensure unique randomness per claim
fn generate_exponential_decay_random(seed: u64, recipient_key: Pubkey) -> Result<u64> {
    const MIN_VAL: f64 = 1.0;
    const MAX_VAL: f64 = 20.0;
    const DECAY_RATE: f64 = 0.4;
    const LAMPORTS_PER_SOL: f64 = 1_000_000_000.0;
    
    // Create a varied seed using a simpler approach
    // Convert pubkey to a single u64 by XORing chunks of bytes
    let recipient_bytes = recipient_key.to_bytes();
    let mut pubkey_hash = 0u64;
    for chunk in recipient_bytes.chunks(8) {
        let mut chunk_val = 0u64;
        for (i, &byte) in chunk.iter().enumerate() {
            chunk_val |= (byte as u64) << (i * 8);
        }
        pubkey_hash ^= chunk_val;
    }
    
    // Combine seed with pubkey hash using multiple operations for better mixing
    let combined_seed = seed
        .wrapping_mul(6364136223846793005u64)
        .wrapping_add(1442695040888963407u64)
        .wrapping_add(pubkey_hash)
        .wrapping_mul(1103515245)
        .wrapping_add(12345);
    
    // Create a simple pseudo-random number generator using the combined seed
    let mut rng_state = combined_seed.wrapping_mul(1103515245).wrapping_add(12345);
    rng_state = rng_state.wrapping_mul(1103515245).wrapping_add(12345);
    
    // Generate uniform random number [0, 1] - this is 'u' in the Python code
    // Use more bits for better precision and ensure we don't get 0
    let u = ((rng_state as f64) / (u64::MAX as f64)).max(f64::EPSILON);
    
    // Apply the exact formula from Python:
    // lambda_val = decay_rate
    // a = min_val  
    // b = max_val
    let lambda_val = DECAY_RATE;
    let a = MIN_VAL;
    let b = MAX_VAL;
    
    // Calculate the normalization factor: norm_factor = 1 - exp(-lambda_val * (b - a))
    let norm_factor = 1.0 - (-lambda_val * (b - a)).exp();
    
    // Apply inverse transform sampling: result = a - (1/lambda_val) * ln(1 - u * norm_factor)
    let ln_input = (1.0 - u * norm_factor).max(f64::EPSILON);
    let result = a - (1.0 / lambda_val) * ln_input.ln();
    
    // Ensure we don't exceed bounds, convert to lamports, and return as u64
    let clamped_result = result.max(a).min(b);
    let lamports_result = (clamped_result * LAMPORTS_PER_SOL) as u64;
    
    Ok(lamports_result)
}

/// Calculates the distribution amount using the bonding curve
fn calculate_distribution_amount(
    virtual_sol_reserves: u64,
    total_supply: u64,
    k_value: u64,
    purchase_amount: u64,
) -> Result<u64> {
    // Each user "buys" a variable amount worth of tokens (purchase_amount is in lamports)
    // The bonding curve formula: tokens = k * total_supply / (k + virtual_sol_reserves)
    // As virtual_sol_reserves increases, fewer tokens are given per unit
    
    let virtual_sol_before = virtual_sol_reserves; // Current virtual SOL reserves
    let virtual_sol_after = virtual_sol_reserves + purchase_amount; // After this claim
    
    // Convert k_value to lamports for calculations (assuming k_value represents SOL units)
    let k_value_lamports = k_value.saturating_mul(1_000_000_000);
    
    // Calculate tokens remaining before this claim
    let tokens_before = if virtual_sol_before == 0 {
        total_supply
    } else {
        let numerator : u128 = (k_value_lamports as u128).saturating_mul(total_supply as u128);
        let denominator : u128 = (k_value_lamports as u128).saturating_add(virtual_sol_before as u128);
        if denominator > 0 {
            (numerator.saturating_div(denominator) as u64).min(total_supply)
        } else {
            0
        }
    };
    
    // Calculate tokens remaining after this claim
    let numerator : u128 = (k_value_lamports as u128).saturating_mul(total_supply as u128);
    let denominator : u128 = (k_value_lamports as u128).saturating_add(virtual_sol_after as u128);
    let tokens_after = if denominator > 0 {
        (numerator.saturating_div(denominator) as u64).min(total_supply)
    } else {
        0
    };
    
    // The distribution amount is the difference
    let distribution_amount = tokens_before.saturating_sub(tokens_after);
    
    Ok(distribution_amount)
}

#[derive(Accounts)]
#[instruction(airdrop_id: u64)]
pub struct CreateAirdrop<'info> {
    #[account(
        init,
        payer = creator,
        space = 8 + 8 + 32 + 32 + 32 + 8 + 8 + 8 + 1 + 1 + 8 + 8 + 8 + 1 + 8 + 1 + 1, // Added 32 bytes for webapp_authority
        seeds = [b"airdrop", creator.key().as_ref(), mint.key().as_ref(), &airdrop_id.to_le_bytes()],
        bump
    )]
    pub airdrop: Account<'info, AirdropAccount>,
    
    #[account(mut)]
    pub creator: Signer<'info>,

    /// The webapp authority that must sign for create and claim operations
    pub webapp_authority: Signer<'info>,
    
    pub mint: InterfaceAccount<'info, Mint>,
    
    #[account(
        mut,
        token::mint = mint,
        token::authority = creator,
        token::token_program = token_program
    )]
    pub creator_token_account: InterfaceAccount<'info, TokenAccount>,
    
    #[account(
        init,
        payer = creator,
        token::mint = mint,
        token::authority = airdrop,
        token::token_program = token_program,
        seeds = [b"vault", airdrop.key().as_ref()],
        bump
    )]
    pub airdrop_vault: InterfaceAccount<'info, TokenAccount>,
    
    pub token_program: Interface<'info, TokenInterface>,
    pub system_program: Program<'info, System>,
    pub rent: Sysvar<'info, Rent>,
}

#[derive(Accounts)]
pub struct DistributeAirdrop<'info> {
    #[account(
        mut,
        seeds = [b"airdrop", airdrop.creator.as_ref(), airdrop.mint.as_ref(), &airdrop.airdrop_id.to_le_bytes()],
        bump = airdrop.bump
    )]
    pub airdrop: Account<'info, AirdropAccount>,
    
    #[account(
        init_if_needed,
        payer = recipient,
        space = 8 + 32 + 32 + 8 + 1 + 1, // discriminator + recipient + airdrop + amount_claimed + has_claimed + bump
        seeds = [b"claim", airdrop.key().as_ref(), recipient.key().as_ref()],
        bump
    )]
    pub claim_record: Account<'info, ClaimRecord>,
    
    #[account(mut)]
    pub recipient: Signer<'info>,

    /// The webapp authority that must sign for create and claim operations
    pub webapp_authority: Signer<'info>,

    #[account(
        constraint = mint.key() == airdrop.mint
    )]
    pub mint: InterfaceAccount<'info, Mint>,
    
    #[account(
        mut,
        token::mint = airdrop.mint,
        token::token_program = token_program
    )]
    pub recipient_token_account: InterfaceAccount<'info, TokenAccount>,
    
    #[account(
        mut,
        token::mint = airdrop.mint,
        token::authority = airdrop,
        token::token_program = token_program,
        seeds = [b"vault", airdrop.key().as_ref()],
        bump
    )]
    pub airdrop_vault: InterfaceAccount<'info, TokenAccount>,
    
    pub token_program: Interface<'info, TokenInterface>,
    pub system_program: Program<'info, System>,
    pub rent: Sysvar<'info, Rent>,
}

#[derive(Accounts)]
pub struct ExpireAirdrop<'info> {
    #[account(
        mut,
        seeds = [b"airdrop", airdrop.creator.as_ref(), airdrop.mint.as_ref(), &airdrop.airdrop_id.to_le_bytes()],
        bump = airdrop.bump
    )]
    pub airdrop: Account<'info, AirdropAccount>,
    
    /// CHECK: This is the creator account, validated through airdrop.creator
    #[account(mut)]
    pub creator: AccountInfo<'info>,

    #[account(
        constraint = mint.key() == airdrop.mint
    )]
    pub mint: InterfaceAccount<'info, Mint>,
    
    #[account(
        mut,
        token::mint = airdrop.mint,
        token::token_program = token_program
    )]
    pub creator_token_account: InterfaceAccount<'info, TokenAccount>,
    
    #[account(
        mut,
        token::mint = airdrop.mint,
        token::authority = airdrop,
        token::token_program = token_program,
        seeds = [b"vault", airdrop.key().as_ref()],
        bump
    )]
    pub airdrop_vault: InterfaceAccount<'info, TokenAccount>,
    
    pub token_program: Interface<'info, TokenInterface>,
}

#[derive(Accounts)]
pub struct CloseAirdrop<'info> {
    #[account(
        mut,
        seeds = [b"airdrop", airdrop.creator.as_ref(), airdrop.mint.as_ref(), &airdrop.airdrop_id.to_le_bytes()],
        bump = airdrop.bump
    )]
    pub airdrop: Account<'info, AirdropAccount>,
    
    #[account(mut)]
    pub creator: Signer<'info>,

    #[account(
        constraint = mint.key() == airdrop.mint
    )]
    pub mint: InterfaceAccount<'info, Mint>,
    
    #[account(
        mut,
        token::mint = airdrop.mint,
        token::authority = creator,
        token::token_program = token_program
    )]
    pub creator_token_account: InterfaceAccount<'info, TokenAccount>,
    
    #[account(
        mut,
        token::mint = airdrop.mint,
        token::authority = airdrop,
        token::token_program = token_program,
        seeds = [b"vault", airdrop.key().as_ref()],
        bump
    )]
    pub airdrop_vault: InterfaceAccount<'info, TokenAccount>,
    
    pub token_program: Interface<'info, TokenInterface>,
}

#[derive(Accounts)]
pub struct RevokeCloseAuthority<'info> {
    #[account(
        mut,
        seeds = [b"airdrop", airdrop.creator.as_ref(), airdrop.mint.as_ref(), &airdrop.airdrop_id.to_le_bytes()],
        bump = airdrop.bump
    )]
    pub airdrop: Account<'info, AirdropAccount>,
    
    pub creator: Signer<'info>,
}

#[derive(Accounts)]
pub struct RechargeAirdrop<'info> {
    #[account(
        mut,
        seeds = [b"airdrop", airdrop.creator.as_ref(), airdrop.mint.as_ref(), &airdrop.airdrop_id.to_le_bytes()],
        bump = airdrop.bump
    )]
    pub airdrop: Account<'info, AirdropAccount>,
    
    #[account(mut)]
    pub recharger: Signer<'info>,

    #[account(
        constraint = mint.key() == airdrop.mint
    )]
    pub mint: InterfaceAccount<'info, Mint>,
    
    #[account(
        mut,
        token::mint = airdrop.mint,
        token::authority = recharger,
        token::token_program = token_program
    )]
    pub recharger_token_account: InterfaceAccount<'info, TokenAccount>,
    
    #[account(
        mut,
        token::mint = airdrop.mint,
        token::authority = airdrop,
        token::token_program = token_program,
        seeds = [b"vault", airdrop.key().as_ref()],
        bump
    )]
    pub airdrop_vault: InterfaceAccount<'info, TokenAccount>,
    
    pub token_program: Interface<'info, TokenInterface>,
}

#[account]
pub struct AirdropAccount {
    pub airdrop_id: u64,                    // 8 bytes - unique identifier
    pub creator: Pubkey,                    // 32 bytes
    pub mint: Pubkey,                       // 32 bytes
    pub webapp_authority: Pubkey,           // 32 bytes
    pub total_supply: u64,                  // 8 bytes
    pub remaining_supply: u64,              // 8 bytes
    pub claims_made: u64,                   // 8 bytes
    pub is_closed: bool,                    // 1 byte
    pub close_authority_revoked: bool,      // 1 byte
    pub created_at: u64,                    // 8 bytes
    pub expiration_time: u64,               // 8 bytes
    pub k_value: u64,                       // 8 bytes
    pub require_unique_wallets: bool,       // 1 byte
    pub virtual_sol_reserves: u64,          // 8 bytes - tracks bonding curve state (in lamports)
    pub use_exponential_decay: bool,        // 1 byte
    pub bump: u8,                           // 1 byte
}

#[account]
pub struct ClaimRecord {
    pub recipient: Pubkey,
    pub airdrop: Pubkey,
    pub amount_claimed: u64,
    pub has_claimed: bool,
    pub bump: u8,
}

#[event]
pub struct AirdropCreated {
    pub airdrop: Pubkey,
    pub creator: Pubkey,
    pub mint: Pubkey,
    pub airdrop_id: u64,
    pub total_supply: u64,
    pub expiration_time: u64,
    pub k_value: u64,
    pub require_unique_wallets: bool,
    pub use_exponential_decay: bool,
    pub revoke_close_authority: bool,
}

#[event]
pub struct TokensDistributed {
    pub airdrop: Pubkey,
    pub recipient: Pubkey,
    pub amount: u64,
    pub claims_made: u64,
}

#[event]
pub struct AirdropClosed {
    pub airdrop: Pubkey,
    pub creator: Pubkey,
    pub tokens_returned: u64,
}

#[event]
pub struct AirdropExpired {
    pub airdrop: Pubkey,
    pub creator: Pubkey,
    pub tokens_returned: u64,
}

#[event]
pub struct CloseAuthorityRevoked {
    pub airdrop: Pubkey,
    pub creator: Pubkey,
}

#[event]
pub struct AirdropRecharged {
    pub airdrop: Pubkey,
    pub recharger: Pubkey,
    pub additional_tokens: u64,
    pub new_total_supply: u64,
    pub new_virtual_sol_reserves: u64,
}

#[error_code]
pub enum AirdropError {
    #[msg("Airdrop is already closed")]
    AirdropClosed,
    #[msg("Recipient has already claimed tokens")]
    AlreadyClaimed,
    #[msg("Insufficient tokens remaining for distribution")]
    InsufficientTokens,
    #[msg("Only the creator can close this airdrop")]
    UnauthorizedClose,
    #[msg("Close authority has been revoked")]
    CloseAuthorityRevoked,
    #[msg("Only the creator can revoke close authority")]
    UnauthorizedRevoke,
    #[msg("Airdrop has expired")]
    AirdropExpired,
    #[msg("Airdrop has not yet expired")]
    AirdropNotExpired,
    #[msg("Total supply must be greater than 0")]
    InvalidTotalSupply,
    #[msg("K value must be greater than 0")]
    InvalidKValue,
    #[msg("Expiration time must be greater than 0")]
    InvalidExpirationTime,
    #[msg("Unauthorized claim")]
    UnauthorizedClaim,
    #[msg("Invalid recharge amount")]
    InvalidRechargeAmount,
} 