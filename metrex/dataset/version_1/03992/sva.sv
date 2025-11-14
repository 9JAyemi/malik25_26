// SVA checker for Test. Bind this into the DUT.
// Example: bind Test Test_sva u_test_sva (.clk(tb_clk), .cnt(cnt), .decr(decr), .next(next));

module Test_sva (
  input logic              clk,
  input logic [3:0]        cnt,
  input logic [6:0]        decr,
  input logic [3:0]        next
);
  default clocking cb @(posedge clk); endclocking

  // Functional correctness
  a_func: assert property (next == (cnt ^ decr[3:0]));

  // Next has no X/Z when driving inputs are known
  a_no_x: assert property (!$isunknown({cnt,decr[3:0]}) |-> !$isunknown(next)));

  // Upper bits of decr are ignored (do not affect next)
  a_upper_indep: assert property ($stable(cnt) && $stable(decr[3:0]) && !$stable(decr[6:4]) |-> $stable(next));

  // Bitwise equivalence and per-bit stimulus coverage
  genvar i;
  for (i=0; i<4; i++) begin : gen_bit
    a_bit_func: assert property (next[i] == (cnt[i] ^ decr[i]));
    // Coverage: toggling cnt[i] alone (within lower nibble) affects next[i]
    c_cnt_bit_affects:  cover property ($changed(cnt[i]) && $stable(cnt[3:i+1]) && $stable(cnt[i-1:0]) && $stable(decr[3:0]) |-> $changed(next[i]));
    // Coverage: toggling decr[i] alone (within lower nibble) affects next[i]
    c_decr_bit_affects: cover property ($changed(decr[i]) && $stable(cnt) && $stable(decr[3:i+1]) && $stable(decr[i-1:0]) |-> $changed(next[i]));
  end

  // Corner-case coverage
  c_all_zero: cover property (cnt==4'h0 && decr[3:0]==4'h0 && next==4'h0);
  c_all_ones: cover property (cnt==4'hF && decr[3:0]==4'hF && next==4'h0);
  c_mix:      cover property (cnt==4'hA && decr[3:0]==4'h5 && next==4'hF);

endmodule

// Optional: immediate assertion for purely combinational checking if no clock is available
// Place in a bind module or testbench scope observing the DUT ports.
module Test_immediate_chk (
  input logic [3:0] cnt,
  input logic [6:0] decr,
  input logic [3:0] next
);
  always_comb begin
    if (!$isunknown({cnt,decr[3:0]}))
      assert (#0 next == (cnt ^ decr[3:0])) else $error("Next != cnt ^ decr[3:0]");
  end
endmodule