// SVA for dff_8_reset
module dff_8_reset_sva (
  input logic        clk,
  input logic        rst,
  input logic [7:0]  d,
  input logic [7:0]  q
);
  default clocking cb @(posedge clk); endclocking

  // Sanity: no X/Z on critical signals
  a_no_x_rst: assert property (!$isunknown(rst));
  a_no_x_q:   assert property (!$isunknown(q));

  // Reset behavior: clears next cycle and holds while asserted
  a_rst_next_zero: assert property (rst |=> (q == 8'h00));
  a_rst_hold_zero: assert property (rst && $past(rst) |-> (q == 8'h00));

  // Normal capture: when not in reset, q follows d on next cycle
  property p_capture_d;
    logic [7:0] d_now;
    (!rst, d_now = d) |=> (q == d_now);
  endproperty
  a_capture_d: assert property (p_capture_d);

  // Coverage
  // 1) Reset pulse then a valid capture after deassertion
  property c_reset_then_cap;
    logic [7:0] d_s;
    rst ##1 (!rst, d_s = d) |=> (q == d_s);
  endproperty
  cover property (c_reset_then_cap);

  // 2) A data change propagates to q on the next cycle
  property c_follow_change;
    logic [7:0] d_now;
    (!rst && $changed(d), d_now = d) |=> (q == d_now && $changed(q));
  endproperty
  cover property (c_follow_change);

endmodule

// Bind into DUT
bind dff_8_reset dff_8_reset_sva sva (.clk(clk), .rst(rst), .d(d), .q(q));