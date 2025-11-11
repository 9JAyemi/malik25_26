// SVA for ripple_carry_adder
// Focused, concise checks and coverage. Bind into DUT scope to access internal 'carry'.

`ifndef SYNTH
bind ripple_carry_adder rca_sva();

module rca_sva;
  default clocking cb @(posedge clk); endclocking

  // Sanity: inputs/outputs known at clock edge
  a_b_rst_known: assert property (!$isunknown({a,b,rst}));
  out_known:      assert property (!$isunknown({sum,carry}));

  // Synchronous reset drives zeros
  reset_zero: assert property (rst |-> (sum==9'd0 && carry==9'd0));

  // Next-state functional equivalence (note: RHS uses previous carry due to NBA)
  next_state_cat: assert property (
    !rst |-> {carry,sum} == {9'd0, (a + b + ($past(rst) ? 9'd0 : $past(carry)))}
  );

  // Equivalent split checks
  sum_lowbits: assert property (
    !rst |-> sum == (a + b + ($past(rst) ? 9'd0 : $past(carry)))[8:0]
  );

  // Structural width effect: upper 8 bits of carry must always be 0; carry[0] is the 10th sum bit
  carry_upper_zero: assert property (!rst |-> carry[8:1]=='0);

  // Coverage
  cover_reset:   cover property (rst ##1 !rst);
  cover_cout:    cover property (!rst && carry[0]);                 // carry-out occurred
  cover_no_cout: cover property (!rst && !carry[0]);                // no carry-out
  cover_min:     cover property (!rst && sum==9'h000 && !carry[0]); // min sum
  cover_max:     cover property (!rst && sum==9'h1FF && carry[0]);  // max sum with carry-out
  cover_2cout:   cover property (!rst && carry[0] ##1 !rst && carry[0]); // consecutive carry-outs
endmodule
`endif