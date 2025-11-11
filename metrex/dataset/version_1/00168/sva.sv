// SVA for top_module
module top_module_sva (
  input logic        clk,
  input logic        reset,
  input logic [7:0]  d,
  input logic [7:0]  q,
  input logic [3:0]  add_out,
  input logic [7:0]  final_out,
  input logic [7:0]  shift_reg,
  input logic [3:0]  counter
);

  default clocking cb @(posedge clk); endclocking

  logic past_valid;
  initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;

  // Basic sanity: no X after first sampled cycle
  assert property (past_valid |-> !$isunknown({shift_reg, counter, q, add_out, final_out}));

  // Synchronous reset behavior
  assert property (reset |-> shift_reg == 8'h34);
  assert property (reset |-> counter   == 4'h0);

  // q mirrors shift_reg
  assert property (q == shift_reg);

  // Shift register next-state (as coded: truncation to 8b implies load of d)
  assert property (past_valid && !$past(reset) |-> shift_reg == $past(d));

  // 4-bit counter increments modulo 16 on non-reset cycles
  assert property (past_valid && !$past(reset)
                   |-> counter == (($past(counter) + 4'd1) & 4'hF));

  // Combinational adder correctness (4-bit wrap)
  assert property (add_out == ((shift_reg[3:0] + counter) & 4'hF));

  // final_out registered sum of previous cycle shift_reg and add_out (zero-extend add_out)
  assert property (past_valid |-> final_out == (($past(shift_reg) + $past(add_out)) & 8'hFF));

  // Coverage
  cover property (reset ##1 !reset);                       // observe a reset deassertion
  cover property (past_valid && $past(counter)==4'hF && !reset && counter==4'h0); // wrap
  cover property (past_valid && !$past(reset) && shift_reg == $past(d));          // normal update
  cover property (add_out==4'h0); 
  cover property (add_out==4'hF);
  cover property (past_valid && final_out != $past(final_out));                   // final_out activity

endmodule

// Bind into DUT (accesses internal shift_reg and counter)
bind top_module top_module_sva sva (
  .clk(clk),
  .reset(reset),
  .d(d),
  .q(q),
  .add_out(add_out),
  .final_out(final_out),
  .shift_reg(shift_reg),
  .counter(counter)
);