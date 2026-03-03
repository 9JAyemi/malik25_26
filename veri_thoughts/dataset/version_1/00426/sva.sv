// SVA for module adder
module adder_sva #(parameter W=16)
(
  input  logic                     clk,
  input  logic                     rst,
  input  logic signed [W-1:0]      a,
  input  logic signed [W-1:0]      b,
  input  logic signed [W-1:0]      sum
);

  default clocking cb @(posedge clk); endclocking

  function automatic signed [W-1:0] add_s(input signed [W-1:0] x, input signed [W-1:0] y);
    add_s = x + y; // 2's complement wrap (matches RTL)
  endfunction

  // Assertions

  // Synchronous reset: next-cycle output is zero
  ap_rst_nxt_zero:        assert property ( $past(rst) |-> sum == '0 );

  // Functional correctness: registered 1-cycle sum when not in reset previous cycle
  ap_sum_correct:         assert property ( !$past(rst) |-> sum == add_s($past(a), $past(b)) );

  // First cycle after reset deassert: compute from deassertion-cycle inputs
  ap_first_after_reset:   assert property ( $fell(rst) |=> sum == add_s($past(a), $past(b)) );

  // Output should never be X/Z once there is at least one cycle of history
  ap_no_x_sum:            assert property ( $past(1'b1) |-> !$isunknown(sum) );

  // While reset remains asserted across cycles, sum stays zero
  ap_hold_zero_while_rst: assert property ( $past(rst) && rst |-> sum == '0 );

  // Coverage

  // See both reset edges
  cv_reset_assert:  cover property ( $rose(rst) );
  cv_reset_release: cover property ( $fell(rst) );

  // Normal operation exercised
  cv_oper:          cover property ( !$past(rst) && sum == add_s($past(a), $past(b)) );

  // Positive overflow (pos + pos -> neg)
  cv_pos_overflow:  cover property ( !$past(rst) && ($past(a[W-1])==0) && ($past(b[W-1])==0) && sum[W-1]==1 );

  // Negative overflow (neg + neg -> pos)
  cv_neg_overflow:  cover property ( !$past(rst) && ($past(a[W-1])==1) && ($past(b[W-1])==1) && sum[W-1]==0 );

  // Zero result (e.g., b == -a)
  cv_zero_sum:      cover property ( !$past(rst) && sum == '0 );

endmodule

// Bind into DUT
bind adder adder_sva #(.W(16)) u_adder_sva (.*);