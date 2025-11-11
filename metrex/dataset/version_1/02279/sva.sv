// SVA for binary_counter
module binary_counter_sva (
  input logic        clk,
  input logic        reset,
  input logic        ena,
  input logic [3:0]  q
);
  default clocking cb @(posedge clk); endclocking

  // Reset behavior
  assert property (reset |=> q == 4'h0);
  assert property ((reset && $past(reset)) |-> q == 4'h0);

  // Hold when disabled (allow reset to preempt)
  assert property ((!reset && !ena) |=> (reset || $stable(q)));

  // Increment when enabled (no wrap)
  assert property ((!reset && ena && q != 4'hF) |=> (reset || q == $past(q) + 4'h1));

  // Wrap when enabled at max
  assert property ((!reset && ena && q == 4'hF) |=> (reset || q == 4'h0));

  // Functional coverage
  cover property (disable iff (reset) (ena && q == 4'hF) ##1 (q == 4'h0));   // wrap covered
  cover property (disable iff (reset) (!ena && $stable(q)));                 // hold covered
  cover property (disable iff (reset) (ena [*16]) ##1 (q == $past(q,16)));   // full cycle when ena held
endmodule

// Bind into DUT
bind binary_counter binary_counter_sva sva_i (.*);