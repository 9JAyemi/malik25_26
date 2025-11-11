// SVA for pipelined_multiplier
// Bind this module; it references internal regs a_reg/b_reg via name matching.
`ifndef PIPELINED_MULTIPLIER_SVA
`define PIPELINED_MULTIPLIER_SVA

module pipelined_multiplier_sva (
  input  logic        clk,
  input  logic        rst,
  input  logic [7:0]  a,
  input  logic [7:0]  b,
  input  logic [7:0]  a_reg,
  input  logic [7:0]  b_reg,
  input  logic [15:0] result
);

  default clocking cb @(posedge clk); endclocking

  // One-cycle latency and functional correctness (skip the cycle right after reset)
  property p_mul_correct;
    !rst && !$past(rst) |-> result == ({8'h00,$past(a)} * {8'h00,$past(b)});
  endproperty
  assert property (p_mul_correct) else $error("Multiplier result mismatch with 1-cycle-latency inputs");

  // Reset clears flops and output (checked on the cycle after rst was high)
  property p_rst_clears;
    $past(rst) |-> (a_reg==8'h00 && b_reg==8'h00 && result==16'h0000);
  endproperty
  assert property (p_rst_clears) else $error("Reset did not clear internal regs/result");

  // Pipeline registers capture inputs (structural check)
  property p_regs_capture;
    disable iff (rst)
      1'b1 |=> (a_reg == $past(a) && b_reg == $past(b));
  endproperty
  assert property (p_regs_capture) else $error("a_reg/b_reg do not capture previous-cycle a/b");

  // No X/Z on primary I/O after pipeline is active
  property p_no_x_after_reset;
    !rst && !$past(rst) |-> !$isunknown({a,b,result});
  endproperty
  assert property (p_no_x_after_reset) else $error("X/Z detected on a/b/result after reset");

  // Functional coverage
  cover property ($past(rst) && !rst);                                   // reset deassertion observed
  cover property (!rst && !$past(rst) && result != 16'h0000);            // first non-zero result
  cover property (!rst && !$past(rst) && ($past(a)==8'h00 || $past(b)==8'h00) && result==16'h0000);
  cover property (!rst && !$past(rst) && $past(a)==8'h01 && result==$past(b));
  cover property (!rst && !$past(rst) && $past(b)==8'h01 && result==$past(a));
  cover property (!rst && !$past(rst) && $past(a)==8'hFF && $past(b)==8'hFF && result==16'hFE01);
  // Two different consecutive input pairs produce two different consecutive results (pipeline activity)
  cover property (!rst && !$past(rst,2) &&
                  {$past(a,2),$past(b,2)} != {$past(a),$past(b)} &&
                  $changed(result));

endmodule

bind pipelined_multiplier pipelined_multiplier_sva sva_bind (.*);

`endif