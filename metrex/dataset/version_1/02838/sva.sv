// SVA for ripple_carry_adder
// Checks 1-cycle latency and full 5-bit addition correctness, plus key coverage.
module ripple_carry_adder_sva (
  input logic        clk,
  input logic [3:0]  A,
  input logic [3:0]  B,
  input logic        carry_in,
  input logic [3:0]  sum,
  input logic        carry_out
);
  default clocking cb @(posedge clk); endclocking

  bit past_valid;
  always_ff @(posedge clk) past_valid <= 1'b1;

  // Core correctness: outputs equal 1-cycle-delayed 5-bit sum of inputs
  property p_add_correct;
    past_valid && !$isunknown($past({A,B,carry_in})) |->
      {carry_out, sum} == ($past({1'b0,A}) + $past({1'b0,B}) + $past(carry_in));
  endproperty
  assert property (p_add_correct);

  // Outputs never X/Z after first valid cycle
  assert property (past_valid |-> !$isunknown({carry_out, sum}));

  // Useful equivalent form for carry_out (redundant but strong)
  assert property (past_valid && !$isunknown($past({A,B,carry_in})) |->
                   carry_out == (($past(A) + $past(B) + $past(carry_in)) > 4'hF));

  // Coverage: see both carry states and key boundary sums
  cover property (past_valid && !carry_out);
  cover property (past_valid &&  carry_out);
  cover property (past_valid && {carry_out,sum} == 5'h00); // total 0
  cover property (past_valid && {carry_out,sum} == 5'h10); // total 16 (wrap)
  cover property (past_valid && {carry_out,sum} == 5'h1F); // total 31 (max)

  // Sum bit activity coverage
  genvar i;
  generate
    for (i = 0; i < 4; i++) begin : g_sum_toggle_cov
      cover property (past_valid && $rose(sum[i]));
      cover property (past_valid && $fell(sum[i]));
    end
  endgenerate
endmodule

// Bind into DUT
bind ripple_carry_adder ripple_carry_adder_sva sva_i (
  .clk(clk),
  .A(A),
  .B(B),
  .carry_in(carry_in),
  .sum(sum),
  .carry_out(carry_out)
);