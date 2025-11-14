// SVA checker for d_ff
module d_ff_sva (
  input  logic clk,
  input  logic reset,
  input  logic set,
  input  logic enable,
  input  logic test,
  input  logic d,
  input  logic q,
  input  logic vpwr,
  input  logic vgnd,
  input  logic dff_in
);
  default clocking cb @(posedge clk); endclocking

  function automatic logic expected_next(input logic set_i, test_i, d_i);
    expected_next = set_i ? 1'b0 : (test_i ? ~d_i : 1'b1);
  endfunction

  wire no_reset_edge = !$rose(reset) && !$fell(reset);

  // X/supply checks
  assert property (!$isunknown(q));
  assert property (vpwr === 1'b1 && vgnd === 1'b0);

  // Reset behavior
  assert property (reset |-> q == 1'b0);

  // Enable/hold behavior (guard against async reset activity in the cycle)
  assert property ((!reset && no_reset_edge && enable) |=> q == expected_next(set, test, d));
  assert property ((!reset && no_reset_edge && !enable) |=> q == $past(q));

  // Output mirrors internal flop (sampled)
  assert property (q == dff_in);

  // Coverage
  cover property ($rose(reset));
  cover property ($fell(reset));
  cover property ((!reset && no_reset_edge && enable && set) |=> q == 1'b0);
  cover property ((!reset && no_reset_edge && enable && !set && !test) |=> q == 1'b1);
  cover property ((!reset && no_reset_edge && enable && !set && test && d) |=> q == 1'b0);
  cover property ((!reset && no_reset_edge && enable && !set && test && !d) |=> q == 1'b1);
  cover property ((!reset && no_reset_edge && !enable) |=> q == $past(q));
endmodule

// Bind SVA to DUT (connects to internal dff_in, vpwr, vgnd as well)
bind d_ff d_ff_sva dff_sva_i (.*);