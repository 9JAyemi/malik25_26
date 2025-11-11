// SVA checker for top_module (and embedded comparator via equal)
module top_module_sva (
  input logic        clk,
  input logic        reset,
  input logic [3:0]  a,
  input logic [3:0]  b,
  input logic        out_func,
  input logic [2:0]  count,
  input logic [2:0]  counter,
  input logic        equal
);
  default clocking cb @(posedge clk); endclocking

  // guard for $past()
  logic past_valid;
  initial past_valid = 1'b0;
  always_ff @(posedge clk) past_valid <= 1'b1;

  // Counter reset behavior
  assert property (reset |=> counter == 3'd0);

  // Counter increments every cycle when not in reset (with wrap)
  assert property (!reset && !$past(reset)
                   |-> ($past(counter) == 3'd7 ? counter == 3'd0
                                               : counter == $past(counter) + 3'd1));

  // count mirrors counter
  assert property (count == counter);

  // out_func reflects comparison using pre-increment counter (same-cycle RHS, sampled next cycle)
  assert property (past_valid |-> out_func == ($past(counter) > $past(b)));

  // If b was >= 8, out_func must be 0 (counter max is 7)
  assert property (past_valid && ($past(b) >= 4'd8) |-> out_func == 1'b0);

  // Comparator correctness (sampled at clk edges; skip when a/b unknown)
  assert property (!$isunknown({a,b}) |-> equal == (a == b));

  // Knownness on key outputs/state after first sample
  assert property (past_valid |-> !$isunknown({counter, count, out_func, equal}));

  // Coverage
  cover property (reset ##1 !reset);                       // reset deassertion observed
  cover property (past_valid && $past(counter)==3'd7 && counter==3'd0); // wrap 7->0
  cover property (out_func == 1'b1);                       // out_func asserted
  cover property (!$isunknown({a,b}) && (a==b) && equal);  // comparator equality seen
  cover property (past_valid && ($past(b) >= 4'd8) && out_func==1'b0); // b>=8 forces 0
endmodule

bind top_module top_module_sva sva_top (
  .clk(clk),
  .reset(reset),
  .a(a),
  .b(b),
  .out_func(out_func),
  .count(count),
  .counter(counter),
  .equal(equal)
);