// SVA for rw_manager_lfsr36
module rw_manager_lfsr36_sva (
  input logic        clk,
  input logic        nrst,
  input logic        ena,
  input logic [35:0] word
);
  default clocking cb @(posedge clk); endclocking
  default disable iff (!nrst);

  localparam logic [35:0] RESET_VAL = 36'hF0F0AA55;

  function automatic logic [35:0] next_word(input logic [35:0] w);
    logic [35:0] n;
    n[35] = w[0];
    n[34] = w[35];
    n[33] = w[34];
    n[32] = w[33];
    n[31] = w[32];
    n[30] = w[31];
    n[29] = w[30];
    n[28] = w[29];
    n[27] = w[28];
    n[26] = w[27];
    n[25] = w[26];
    n[24] = w[25] ^ w[0];
    n[23] = w[24];
    n[22] = w[23];
    n[21] = w[22];
    n[20] = w[21];
    n[19] = w[20];
    n[18] = w[19];
    n[17] = w[18];
    n[16] = w[17];
    n[15] = w[16];
    n[14] = w[15];
    n[13] = w[14];
    n[12] = w[13];
    n[11] = w[12];
    n[10] = w[11];
    n[9]  = w[10];
    n[8]  = w[9];
    n[7]  = w[8];
    n[6]  = w[7];
    n[5]  = w[6];
    n[4]  = w[5];
    n[3]  = w[4];
    n[2]  = w[3];
    n[1]  = w[2];
    n[0]  = w[1];
    return n;
  endfunction

  // Reset value must be driven while reset is active (override default disable)
  assert property (disable iff (1'b0) !nrst |-> word == RESET_VAL);

  // No X/Z out of reset
  assert property (!$isunknown(word));

  // Hold when disabled
  assert property (!ena |-> $stable(word));

  // Correct next-state function when enabled (skip first cycle after reset)
  assert property (ena && $past(nrst) |-> word == next_word($past(word)));

  // On reset release, next sampled value equals reset or next(reset) based on ena
  assert property (disable iff (1'b0) $rose(nrst) |-> (ena ? word == next_word(RESET_VAL)
                                                          : word == RESET_VAL));

  // All-zero state must never be observed out of reset
  assert property (word != 36'b0);

  // Coverage
  cover property (disable iff (1'b0) $fell(nrst));
  cover property (disable iff (1'b0) $rose(nrst));
  cover property (ena && $past(nrst) ##1 word == next_word($past(word,1)));
  cover property (!ena ##1 $stable(word));
  cover property (##1 $changed(word));
endmodule

bind rw_manager_lfsr36 rw_manager_lfsr36_sva sva_i(.clk(clk), .nrst(nrst), .ena(ena), .word(word));