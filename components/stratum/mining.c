#include <string.h>
#include <stdio.h>
#include <limits.h>
#include "mining.h"
#include "utils.h"
#include "mbedtls/sha256.h"
#include "esp_log.h"

// Set to 1 to use midstate optimization for nonce validation, 0 for full header hash
#define USE_MIDSTATE_VALIDATION 1

void free_bm_job(bm_job *job)
{
    free(job->jobid);
    free(job->extranonce2);
    free(job);
}

void calculate_coinbase_tx_hash(const char *coinbase_1, const char *coinbase_2, const char *extranonce, const char *extranonce_2, uint8_t dest[32])
{
    size_t len1 = strlen(coinbase_1);
    size_t len2 = strlen(extranonce);
    size_t len3 = strlen(extranonce_2);
    size_t len4 = strlen(coinbase_2);

    size_t coinbase_tx_bin_len = (len1 + len2 + len3 + len4) / 2;

    uint8_t coinbase_tx_bin[coinbase_tx_bin_len];

    size_t bin_offset = 0;
    bin_offset += hex2bin(coinbase_1, coinbase_tx_bin + bin_offset, coinbase_tx_bin_len - bin_offset);
    bin_offset += hex2bin(extranonce, coinbase_tx_bin + bin_offset, coinbase_tx_bin_len - bin_offset);
    bin_offset += hex2bin(extranonce_2, coinbase_tx_bin + bin_offset, coinbase_tx_bin_len - bin_offset);
    bin_offset += hex2bin(coinbase_2, coinbase_tx_bin + bin_offset, coinbase_tx_bin_len - bin_offset);

    double_sha256_bin(coinbase_tx_bin, coinbase_tx_bin_len, dest);
}

void calculate_merkle_root_hash(const uint8_t coinbase_tx_hash[32], const uint8_t merkle_branches[][32], const int num_merkle_branches, uint8_t dest[32])
{
    uint8_t both_merkles[64];
    memcpy(both_merkles, coinbase_tx_hash, 32);
    for (int i = 0; i < num_merkle_branches; i++) {
        memcpy(both_merkles + 32, merkle_branches[i], 32);
        double_sha256_bin(both_merkles, 64, both_merkles);
    }

    memcpy(dest, both_merkles, 32);
}

// take a mining_notify struct with ascii hex strings and convert it to a bm_job struct
void construct_bm_job(mining_notify *params, const uint8_t merkle_root[32], const uint32_t version_mask, const uint32_t difficulty, bm_job *new_job)
{
    new_job->version = params->version;
    new_job->version_mask = version_mask;
    new_job->target = params->target;
    new_job->ntime = params->ntime;
    new_job->starting_nonce = 0;
    new_job->pool_diff = difficulty;
    reverse_32bit_words(merkle_root, new_job->merkle_root);

    uint8_t prev_block_hash[32];
    hex2bin(params->prev_block_hash, prev_block_hash, 32);
    reverse_endianness_per_word(prev_block_hash);
    reverse_32bit_words(prev_block_hash, new_job->prev_block_hash);

    // make the midstate hash
    uint8_t midstate_data[64];

    // copy 64 bytes header data into midstate (and deal with endianess)
    memcpy(midstate_data, &new_job->version, 4);      // copy version
    memcpy(midstate_data + 4, prev_block_hash, 32);   // copy prev_block_hash
    memcpy(midstate_data + 36, merkle_root, 28);      // copy merkle_root

    uint8_t midstate[32];
    midstate_sha256_bin(midstate_data, 64, midstate); // make the midstate hash
    reverse_32bit_words(midstate, new_job->midstate); // reverse the midstate words for the BM job packet

    if (version_mask != 0)
    {
        uint32_t rolled_version = increment_bitmask(new_job->version, version_mask);
        memcpy(midstate_data, &rolled_version, 4);
        midstate_sha256_bin(midstate_data, 64, midstate);
        reverse_32bit_words(midstate, new_job->midstate1);

        rolled_version = increment_bitmask(rolled_version, version_mask);
        memcpy(midstate_data, &rolled_version, 4);
        midstate_sha256_bin(midstate_data, 64, midstate);
        reverse_32bit_words(midstate, new_job->midstate2);

        rolled_version = increment_bitmask(rolled_version, version_mask);
        memcpy(midstate_data, &rolled_version, 4);
        midstate_sha256_bin(midstate_data, 64, midstate);
        reverse_32bit_words(midstate, new_job->midstate3);
        new_job->num_midstates = 4;
    }
    else
    {
        new_job->num_midstates = 1;
    }
}

void extranonce_2_generate(uint64_t extranonce_2, uint32_t length, char dest[static length * 2 + 1])
{
    // Allocate buffer to hold the extranonce_2 value in bytes
    uint8_t extranonce_2_bytes[length];
    memset(extranonce_2_bytes, 0, length);
    
    // Copy the extranonce_2 value into the buffer, handling endianness
    // Copy up to the size of uint64_t or the requested length, whichever is smaller
    size_t copy_len = (length < sizeof(uint64_t)) ? length : sizeof(uint64_t);
    memcpy(extranonce_2_bytes, &extranonce_2, copy_len);
    
    // Convert the bytes to hex string
    bin2hex(extranonce_2_bytes, length, dest, length * 2 + 1);
}

///////cgminer nonce testing
/* truediffone == 0x00000000FFFF0000000000000000000000000000000000000000000000000000
 */
static const double truediffone = 26959535291011309493156476344723991336010898738574164086137773096960.0;

// Select the correct midstate based on rolled_version, returns NULL if no match
static const uint8_t * select_midstate(const bm_job *job, const uint32_t rolled_version)
{
    if (rolled_version == job->version) {
        return job->midstate;
    }
    if (job->num_midstates < 2) {
        return NULL;
    }
    
    uint32_t v = increment_bitmask(job->version, job->version_mask);
    if (rolled_version == v) {
        return job->midstate1;
    }
    if (job->num_midstates < 3) {
        return NULL;
    }
    
    v = increment_bitmask(v, job->version_mask);
    if (rolled_version == v) {
        return job->midstate2;
    }
    if (job->num_midstates < 4) {
        return NULL;
    }
    
    v = increment_bitmask(v, job->version_mask);
    if (rolled_version == v) {
        return job->midstate3;
    }
    
    return NULL;
}

/* testing a nonce and return the diff - 0 means invalid */
double test_nonce_value(const bm_job *job, const uint32_t nonce, const uint32_t rolled_version)
{
    uint8_t hash_result[32];
    
#if USE_MIDSTATE_VALIDATION
    // Try to use precomputed midstate for faster validation
    const uint8_t *midstate_reversed = select_midstate(job, rolled_version);
    
    if (midstate_reversed != NULL) {
        // Optimized path: continue SHA256 from midstate
        // The midstate is stored reversed for ASIC, so un-reverse it
        uint8_t midstate[32];
        reverse_32bit_words(midstate_reversed, midstate);
        
        // Set up SHA256 context with midstate
        mbedtls_sha256_context ctx;
        mbedtls_sha256_init(&ctx);
        mbedtls_sha256_starts(&ctx, 0);
        
        // Restore state from midstate (state is 8 x uint32_t = 32 bytes)
        memcpy(ctx.state, midstate, 32);
        ctx.total[0] = 64;  // 64 bytes already processed
        ctx.total[1] = 0;
        
        // Build the remaining 16 bytes of header (bytes 64-79)
        // Header layout: version(4) + prev_hash(32) + merkle_root(32) + ntime(4) + nbits(4) + nonce(4)
        // Midstate covers bytes 0-63, so remaining is: merkle_root[28:32] + ntime + nbits + nonce
        uint8_t remaining[16];
        uint8_t merkle_root_unreversed[32];
        reverse_32bit_words(job->merkle_root, merkle_root_unreversed);
        memcpy(remaining, merkle_root_unreversed + 28, 4);  // last 4 bytes of merkle_root
        memcpy(remaining + 4, &job->ntime, 4);
        memcpy(remaining + 8, &job->target, 4);
        memcpy(remaining + 12, &nonce, 4);
        
        // Continue hashing and finalize
        mbedtls_sha256_update(&ctx, remaining, 16);
        uint8_t first_hash[32];
        mbedtls_sha256_finish(&ctx, first_hash);
        mbedtls_sha256_free(&ctx);
        
        // Second SHA256
        mbedtls_sha256(first_hash, 32, hash_result, 0);
    } else
#endif
    {
        // Full header hash path
        uint8_t header[80];
        memcpy(header, &rolled_version, 4);
        reverse_32bit_words(job->prev_block_hash, header + 4);
        reverse_32bit_words(job->merkle_root, header + 36);
        memcpy(header + 68, &job->ntime, 4);
        memcpy(header + 72, &job->target, 4);
        memcpy(header + 76, &nonce, 4);
        
        double_sha256_bin(header, 80, hash_result);
    }

    double d64 = truediffone;
    double s64 = le256todouble(hash_result);
    return d64 / s64;
}

uint32_t increment_bitmask(const uint32_t value, uint32_t mask)
{
    uint32_t new_value = value;

    // Iteratively handle carry propagation (replaces recursive implementation)
    while (mask != 0)
    {
        uint32_t carry = (new_value & mask) + (mask & -mask); // increment the least significant bit of the mask
        uint32_t overflow = carry & ~mask;                    // find overflowed bits that are not in the mask
        new_value = (new_value & ~mask) | (carry & mask);     // set bits according to the mask

        if (overflow == 0)
            break;

        mask = overflow << 1; // shift left to get the mask where carry should be propagated
    }

    return new_value;
}
