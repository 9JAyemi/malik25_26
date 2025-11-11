// SVA checker for RCB_FRL_CRC_gen
// Focused, bindable, clockless (uses $global_clock), with equivalence, stability,
// single-bit influence, X-propagation checks, and concise coverage.

module RCB_FRL_CRC_gen_sva (
  input logic [47:0] D,
  input logic [7:0]  NewCRC
);

  default clocking cb @($global_clock); endclocking

  // Golden combinational function (mirrors DUT equations)
  function automatic logic [7:0] crc_from_D (input logic [47:0] D);
    logic [7:0] c;
    c[0] = D[46] ^ D[42] ^ D[41] ^ D[37] ^ D[36] ^ D[35] ^ D[34] ^
           D[33] ^ D[31] ^ D[30] ^ D[29] ^ D[27] ^ D[26] ^ D[24] ^
           D[20] ^ D[18] ^ D[17] ^ D[16] ^ D[15] ^ D[14] ^ D[13] ^
           D[8]  ^ D[7]  ^ D[6]  ^ D[3]  ^ D[1]  ^ D[0];
    c[1] = D[47] ^ D[43] ^ D[42] ^ D[38] ^ D[37] ^ D[36] ^ D[35] ^
           D[34] ^ D[32] ^ D[31] ^ D[30] ^ D[28] ^ D[27] ^ D[25] ^
           D[21] ^ D[19] ^ D[18] ^ D[17] ^ D[16] ^ D[15] ^ D[14] ^
           D[9]  ^ D[8]  ^ D[7]  ^ D[4]  ^ D[2]  ^ D[1];
    c[2] = D[46] ^ D[44] ^ D[43] ^ D[42] ^ D[41] ^ D[39] ^ D[38] ^
           D[34] ^ D[32] ^ D[30] ^ D[28] ^ D[27] ^ D[24] ^ D[22] ^
           D[19] ^ D[14] ^ D[13] ^ D[10] ^ D[9]  ^ D[7]  ^ D[6]  ^
           D[5]  ^ D[2]  ^ D[1]  ^ D[0];
    c[3] = D[47] ^ D[45] ^ D[44] ^ D[43] ^ D[42] ^ D[40] ^ D[39] ^
           D[35] ^ D[33] ^ D[31] ^ D[29] ^ D[28] ^ D[25] ^ D[23] ^
           D[20] ^ D[15] ^ D[14] ^ D[11] ^ D[10] ^ D[8]  ^ D[7]  ^
           D[6]  ^ D[3]  ^ D[2]  ^ D[1];
    c[4] = D[45] ^ D[44] ^ D[43] ^ D[42] ^ D[40] ^ D[37] ^ D[35] ^
           D[33] ^ D[32] ^ D[31] ^ D[27] ^ D[21] ^ D[20] ^ D[18] ^
           D[17] ^ D[14] ^ D[13] ^ D[12] ^ D[11] ^ D[9]  ^ D[6]  ^
           D[4]  ^ D[2]  ^ D[1]  ^ D[0];
    c[5] = D[46] ^ D[45] ^ D[44] ^ D[43] ^ D[41] ^ D[38] ^ D[36] ^
           D[34] ^ D[33] ^ D[32] ^ D[28] ^ D[22] ^ D[21] ^ D[19] ^
           D[18] ^ D[15] ^ D[14] ^ D[13] ^ D[12] ^ D[10] ^ D[7]  ^
           D[5]  ^ D[3]  ^ D[2]  ^ D[1];
    c[6] = D[47] ^ D[45] ^ D[44] ^ D[41] ^ D[39] ^ D[36] ^ D[31] ^
           D[30] ^ D[27] ^ D[26] ^ D[24] ^ D[23] ^ D[22] ^ D[19] ^
           D[18] ^ D[17] ^ D[11] ^ D[7]  ^ D[4]  ^ D[2]  ^ D[1]  ^
           D[0];
    c[7] = D[45] ^ D[41] ^ D[40] ^ D[36] ^ D[35] ^ D[34] ^ D[33] ^
           D[32] ^ D[30] ^ D[29] ^ D[28] ^ D[26] ^ D[25] ^ D[23] ^
           D[19] ^ D[17] ^ D[16] ^ D[15] ^ D[14] ^ D[13] ^ D[12] ^
           D[7]  ^ D[6]  ^ D[5]  ^ D[2]  ^ D[0];
    return c;
  endfunction

  // Per-input-bit influence masks: NewCRC ^ $past(NewCRC) when only D[i] toggles
  localparam logic [7:0] CRC_MASK [0:47] = '{
    8'hD5, 8'h7F, 8'hFE, 8'h29, 8'h52, 8'hA4, 8'h9F, 8'hEF,
    8'h0B, 8'h16, 8'h2C, 8'h58, 8'hB0, 8'hB7, 8'hBF, 8'hAB,
    8'h83, 8'hD3, 8'h73, 8'hE6, 8'h19, 8'h32, 8'h64, 8'hC8,
    8'h45, 8'h8A, 8'hC1, 8'h77, 8'hAE, 8'h89, 8'hC7, 8'h5B,
    8'hB6, 8'hB9, 8'hA7, 8'h9B, 8'hE3, 8'h13, 0,      8'h4C,
    8'h98, 8'hE5, 8'h3F, 8'h3E, 8'h7C, 8'hF8, 8'h25, 8'h4A
  };

  // Functional equivalence: DUT output equals golden function
  assert property (NewCRC == crc_from_D(D))
    else $error("RCB_FRL_CRC_gen: NewCRC mismatch for D=%h (got=%h exp=%h)", D, NewCRC, crc_from_D(D));

  // Knownness: when inputs are 0/1, outputs must be 0/1
  assert property (!$isunknown(D) |-> !$isunknown(NewCRC))
    else $error("RCB_FRL_CRC_gen: X/Z observed on NewCRC for known D");

  // Combinational stability: if inputs are stable, outputs stay stable
  assert property ($stable(D) |=> $stable(NewCRC))
    else $error("RCB_FRL_CRC_gen: NewCRC changed without D change");

  // Single-bit sensitivity and correct toggle mask
  genvar i;
  generate
    for (i = 0; i < 48; i++) begin : g_mask
      property p_singlebit;
        (!$isunknown(D) && !$isunknown($past(D)) &&
         ((D ^ $past(D)) == (48'h1 << i)))
        |-> ((NewCRC ^ $past(NewCRC)) == CRC_MASK[i]);
      endproperty
      assert property (p_singlebit)
        else $error("RCB_FRL_CRC_gen: Wrong toggle mask for D[%0d]", i);

      // Cover that each single-bit toggle scenario is exercised
      cover property ((D ^ $past(D)) == (48'h1 << i));
    end
  endgenerate

  // Basic output activity coverage: each CRC bit rises and falls at least once
  genvar j;
  generate
    for (j = 0; j < 8; j++) begin : g_cov_out
      cover property ($rose(NewCRC[j]));
      cover property ($fell(NewCRC[j]));
    end
  endgenerate

endmodule

bind RCB_FRL_CRC_gen RCB_FRL_CRC_gen_sva sva_i (.*);