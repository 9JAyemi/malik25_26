// SVA for multiplier_block: checks structure and end-to-end behavior, plus key coverage.
// Bind this file to the DUT.

module multiplier_block_sva (
  input logic [31:0] i_data0,
  input logic [31:0] o_data0,
  input logic [31:0] w1,
  input logic [31:0] w512,
  input logic [31:0] w511,
  input logic [31:0] w64,
  input logic [31:0] w575,
  input logic [31:0] w2300,
  input logic [31:0] w2875
);

  default clocking cb @($global_clock); endclocking

  function automatic logic [31:0] mul2875_mod32(input logic [31:0] x);
    mul2875_mod32 = ($unsigned(x) * 32'd2875)[31:0];
  endfunction

  // Structural equivalence of all intermediate nets
  assert property (
       (w1    == i_data0)
    && (w512  == (w1    << 9))
    && (w64   == (w1    << 6))
    && (w511  == (w512  -  w1))
    && (w575  == (w511  +  w64))
    && (w2300 == (w575  << 2))
    && (w2875 == (w575  +  w2300))
    && (o_data0 == w2875)
  ) else $error("Structural mismatch in multiplier_block datapath");

  // End-to-end functional check (modulo 2^32)
  assert property (o_data0 == mul2875_mod32(i_data0))
    else $error("Functional mismatch: o_data0 != i_data0 * 2875 (mod 2^32)");

  // X/Z propagation guard: when input is known, all internals and output must be known
  assert property ( !$isunknown(i_data0) |-> !$isunknown({w1,w512,w64,w511,w575,w2300,w2875,o_data0}) )
    else $error("X/Z detected in datapath with known input");

  // Coverage: key values and overflow behavior
  cover property (i_data0 == 32'd0 && o_data0 == 32'd0);
  cover property (i_data0 == 32'd1 && o_data0 == 32'd2875);
  cover property (i_data0 == 32'hFFFF_FFFF);
  cover property (i_data0[31] == 1'b1); // high-bit set cases
  cover property ( (($unsigned(i_data0) * 32'd2875)[63:32]) != 0 ); // product overflow
  cover property ( (($unsigned(i_data0) * 32'd2875)[63:32]) == 0 ); // product fits in 32b

endmodule

bind multiplier_block multiplier_block_sva u_multiplier_block_sva (
  .i_data0(i_data0),
  .o_data0(o_data0),
  .w1(w1),
  .w512(w512),
  .w511(w511),
  .w64(w64),
  .w575(w575),
  .w2300(w2300),
  .w2875(w2875)
);