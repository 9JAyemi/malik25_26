// SVA bind file for multiplier and top_module
// Focus: precise functional relations, reset semantics, basic X checks, and concise coverage.

`ifndef MULTIPLIER_SVA
`define MULTIPLIER_SVA

// Assertions for multiplier
module mult_sva_bind
(
  input logic        clk,
  input logic        rst,
  input logic [15:0] in1,
  input logic [15:0] in2,
  input logic [31:0] out,
  input logic [15:0] shift_reg, // internal
  input logic [31:0] sum_reg    // internal
);

  default clocking cb @(posedge clk); endclocking

  // Track past_valid and whether reset has ever been asserted
  logic past_valid, seen_reset;
  always_ff @(posedge clk) begin
    past_valid <= 1'b1;
    if (rst) seen_reset <= 1'b1;
  end

  // Reset behavior
  assert property (rst |-> (shift_reg == 16'h0 && sum_reg == 32'h0 && $stable(out)))
    else $error("multiplier: reset did not clear regs and/or hold out stable");

  // Sequential update relations (use previous-cycle state; disable during reset)
  // out_n = sum_reg_{n-1} + (in1[0]_n ? shift_reg_{n-1} : in2_n)
  assert property (disable iff (rst)
                   past_valid && !$past(rst)
                   |-> out == $past(sum_reg) + (in1[0] ? $past(shift_reg) : in2))
    else $error("multiplier: out update relation failed");

  // sum_reg_n = out_{n-1}
  assert property (disable iff (rst)
                   past_valid && !$past(rst)
                   |-> sum_reg == $past(out))
    else $error("multiplier: sum_reg != past(out)");

  // shift_reg_n = {shift_reg_{n-1}[14:0], in2[0]_n}
  assert property (disable iff (rst)
                   past_valid && !$past(rst)
                   |-> shift_reg == {$past(shift_reg[14:0]), in2[0]})
    else $error("multiplier: shift_reg shift/append relation failed");

  // No X after at least one reset deassertion (stronger check gated by seen_reset)
  assert property (disable iff (rst)
                   seen_reset |-> !$isunknown({out, sum_reg, shift_reg}))
    else $error("multiplier: X detected after reset deassertion");

  // Minimal functional coverage
  cover property (past_valid && !rst && !$past(rst) && (in1[0] == 1'b0));
  cover property (past_valid && !rst && !$past(rst) && (in1[0] == 1'b1));
  cover property (past_valid && !rst && !$past(rst) ##1 !rst); // 2+ consecutive active cycles
  cover property ($rose(rst)); // observe a reset pulse at least once

endmodule

bind multiplier mult_sva_bind
(
  .clk       (clk),
  .rst       (rst),
  .in1       (in1),
  .in2       (in2),
  .out       (out),
  .shift_reg (shift_reg),
  .sum_reg   (sum_reg)
);

// Assertions for top_module
module top_sva_bind
(
  input logic        clk,
  input logic [15:0] in1,
  input logic [15:0] in2,
  input logic [31:0] out,
  input logic [31:0] mult_out
);
  default clocking cb @(posedge clk); endclocking

  // Combinational add correctness at sample points
  assert property (out == (in1 + in2 + mult_out))
    else $error("top_module: out != in1 + in2 + mult_out");

  // Basic coverage of activity
  cover property ($changed(in1) || $changed(in2) || $changed(mult_out));
endmodule

bind top_module top_sva_bind
(
  .clk      (clk),
  .in1      (in1),
  .in2      (in2),
  .out      (out),
  .mult_out (mult_out)
);

`endif