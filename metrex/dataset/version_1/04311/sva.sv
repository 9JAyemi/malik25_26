// SVA for adder_reg
// Bind-friendly checker that reaches internal "sum"

module adder_reg_sva (
  input  logic        clk,
  input  logic        reset,
  input  logic [3:0]  a,
  input  logic [3:0]  b,
  input  logic        select,
  input  logic [7:0]  q,
  input  logic [3:0]  sum
);

  default clocking cb @(posedge clk); endclocking

  logic past_valid;
  always @(posedge clk) past_valid <= 1'b1;

  // Synchronous reset drives both regs low next cycle
  assert property (reset |=> (sum == 4'h0 && q == 8'h00));

  // q is always the zero-extended previous sum (one-cycle pipeline)
  assert property (past_valid |-> (q == {4'h0, $past(sum)}));

  // When select=0, sum updates to a+b (4-bit wrap) on the next cycle
  assert property (disable iff (reset)
                   (!select) |=> (sum == (($past(a)+$past(b)) & 4'hF)));

  // When select=1, sum holds its value
  assert property (disable iff (reset)
                   (select) |=> (sum == $past(sum)));

  // No X/Z on state/outputs after reset
  assert property (disable iff (reset) !$isunknown({sum, q}));

  // --------------------------------
  // Functional coverage
  // --------------------------------
  // Reset followed by add then hold
  cover property (reset ##1 !reset ##1 (!select) ##1 (select));

  // Back-to-back add updates
  cover property (disable iff (reset) (!select ##1 !select));

  // Adder overflow case (wrap)
  cover property (disable iff (reset) (!select && ((a + b) > 4'hF)));

  // q changes (pipeline visible)
  cover property (past_valid && (q != $past(q)));

endmodule

// Bind into DUT
bind adder_reg adder_reg_sva u_adder_reg_sva (
  .clk    (clk),
  .reset  (reset),
  .a      (a),
  .b      (b),
  .select (select),
  .q      (q),
  .sum    (sum)
);