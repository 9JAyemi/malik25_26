// SVA checker for tkl5x1
module tkl5x1_sva (
  input  logic        clk,
  input  logic        reset,
  input  logic [4:0]  i_0r0,
  input  logic [4:0]  i_0r1,
  input  logic        i_0a,
  input  logic [4:0]  o_0r0,
  input  logic [4:0]  o_0r1,
  input  logic        o_0a
);
  default clocking cb @(posedge clk); endclocking

  // Functional correctness
  ap_r0_func: assert property (disable iff (reset)
    o_0r0 == (i_0r0 | (i_0r1 & {5{i_0a}}))
  );
  ap_r1_func: assert property (disable iff (reset)
    o_0r1 == (i_0r0 | (i_0r1 & {5{i_0a}}))
  );
  ap_r_eq: assert property (disable iff (reset)
    o_0r0 == o_0r1
  );
  ap_oa_func: assert property (disable iff (reset)
    o_0a == &o_0r0[3:0]
  );

  // Purely combinational: no hidden state
  ap_pure_comb: assert property (
    $stable({i_0r0,i_0r1,i_0a}) |=> $stable({o_0r0,o_0r1,o_0a})
  );

  // X/Z propagation guard
  ap_no_xprop: assert property (
    !$isunknown({i_0r0,i_0r1,i_0a}) |-> !$isunknown({o_0r0,o_0r1,o_0a})
  );

  // Reset independence (reset is unused in DUT)
  ap_reset_indep: assert property (
    $changed(reset) && $stable({i_0r0,i_0r1,i_0a}) |=> $stable({o_0r0,o_0r1,o_0a})
  );

  // Covers
  cp_a0_path:  cover property (!reset && (i_0a==1'b0) && (o_0r0==i_0r0));
  cp_a1_path:  cover property (!reset && (i_0a==1'b1) && (o_0r0==(i_0r0 | i_0r1)));
  cp_r1_effect: cover property (!reset && i_0a && (|(i_0r1 & ~i_0r0))); // r1 actually contributes
  cp_oa_high:  cover property (!reset && o_0a);                          // lower nibble all ones
endmodule

// Example bind (requires a clock visible in the DUT's parent scope)
bind tkl5x1 tkl5x1_sva sva_u (
  .clk   (clk),
  .reset (reset),
  .i_0r0 (i_0r0),
  .i_0r1 (i_0r1),
  .i_0a  (i_0a),
  .o_0r0 (o_0r0),
  .o_0r1 (o_0r1),
  .o_0a  (o_0a)
);