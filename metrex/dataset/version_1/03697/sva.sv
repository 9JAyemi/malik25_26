// SVA for accumulator
module accumulator_sva #(parameter int n = 8)
(
  input  logic              clk,
  input  logic              rst,
  input  logic [n-1:0]      in,
  input  logic [n-1:0]      sum, // internal reg (bound hierarchically)
  input  logic [n-1:0]      out
);

default clocking cb @(posedge clk); endclocking

// Core correctness
a_out_mux:          assert property (out == (rst ? '0 : sum));
a_reset_clears:     assert property (rst |-> sum == '0);
a_update_after_rst: assert property (!rst &&  $past(rst) |-> sum == $past(in));
a_update_steady:    assert property (!rst && !$past(rst) |-> sum == $past(sum) + $past(in));

// Useful coverpoints
c_reset_then_run:   cover  property (rst ##1 !rst);
c_accumulate:       cover  property (!rst && !$past(rst) && $past(in) != '0 &&
                                      sum == $past(sum) + $past(in));
c_hold_when_zero:   cover  property (!rst && !$past(rst) && $past(in) == '0 &&
                                      sum == $past(sum));
c_wraparound:       cover  property (!rst && !$past(rst) && $past(in) != '0 &&
                                      (sum < $past(sum)));
c_long_reset:       cover  property (rst [*2]);

endmodule

// Bind into DUT (accesses internal 'sum')
bind accumulator accumulator_sva #(.n(n))
  accumulator_sva_i (.clk(clk), .rst(rst), .in(in), .sum(sum), .out(out));