// SVA checker for shift_register
module shift_register_sva (
  input logic        clk,
  input logic        reset,
  input logic [7:0]  d,
  input logic [7:0]  q,
  input logic [7:0]  shift_reg
);

  default clocking cb @(posedge clk); endclocking

  // Asynchronous reset must clear immediately
  ap_async_clear: assert property (@(posedge reset) ##0 (q == 8'h00));

  // While reset is high at a clock edge, output must be 0
  ap_hold_during_reset: assert property (reset |-> (q == 8'h00));

  // Output must mirror internal register
  ap_q_matches_reg: assert property (q == shift_reg);

  // Shift behavior when no reset now or in prior sampled clock
  ap_shift_correct: assert property (
    disable iff (reset)
    (!$isunknown($past(q)) && !$past(reset)) |-> 
      (q == { $past(q)[6:0], $past(d[0]) })
  );

  // Bitwise view (redundant but precise): MSBs shift up, LSB loads d[0]
  ap_bits_move: assert property (
    disable iff (reset)
    (!$isunknown($past(q)) && !$past(reset)) |-> 
      (q[7:1] == $past(q[6:0]) && q[0] == $past(d[0]))
  );

  // No X on q when prior state and input bit were known
  ap_no_x_when_known: assert property (
    disable iff (reset)
    !$isunknown($past(q)) && !$isunknown($past(d[0])) |-> !$isunknown(q)
  );

  // Coverage
  cp_reset_assert:  cover property (@(posedge reset) 1);
  cp_reset_release: cover property ($fell(reset));
  cp_lsb_load_1:    cover property (!reset && $rose(q[0]));
  cp_lsb_load_0:    cover property (!reset && $fell(q[0]));
  cp_reach_msb:     cover property (!reset && $rose(q[7]));

endmodule

// Bind into DUT
bind shift_register shift_register_sva u_shift_register_sva (
  .clk(clk),
  .reset(reset),
  .d(d),
  .q(q),
  .shift_reg(shift_reg)
);