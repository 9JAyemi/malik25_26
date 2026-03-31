module counter_mod_rtl_sva (
  input logic clk,
  input logic rst,
  input logic up_down,
  input logic [3:0] q,
  input logic carry
);

  // Reset drives q and carry LOW when rst is HIGH at the clock edge.
  check_reset_outputs: assert property (
    @(posedge clk) rst |-> (q == 4'b0000) && (carry == 1'b0)
  );

  // Up-count non-wrap: if last q != 15 and up mode, next q = q+1 and carry=0.
  check_up_nonwrap_next: assert property (
    @(posedge clk) disable iff (rst)
      (!$past(rst) && (up_down == 1'b0) && ($past(q) != 4'hF))
      |-> (q == $past(q) + 4'd1) && (carry == 1'b0)
  );

  // Up-count wrap: if last q == 15 and up mode, next q = 0 and carry=1.
  check_up_wrap_next: assert property (
    @(posedge clk) disable iff (rst)
      (!$past(rst) && (up_down == 1'b0) && ($past(q) == 4'hF))
      |-> (q == 4'd0) && (carry == 1'b1)
  );

  // Down-count non-wrap: if last q != 0 and down mode, next q = q-1 and carry=0.
  check_down_nonwrap_next: assert property (
    @(posedge clk) disable iff (rst)
      (!$past(rst) && (up_down == 1'b1) && ($past(q) != 4'd0))
      |-> (q == $past(q) - 4'd1) && (carry == 1'b0)
  );

  // Down-count wrap: if last q == 0 and down mode, next q = 15 and carry=1.
  check_down_wrap_next: assert property (
    @(posedge clk) disable iff (rst)
      (!$past(rst) && (up_down == 1'b1) && ($past(q) == 4'd0))
      |-> (q == 4'hF) && (carry == 1'b1)
  );

  // Carry definition: carry is 1 iff a wrap occurs based on direction and last q.
  check_carry_definition: assert property (
    @(posedge clk) disable iff (rst)
      (!$past(rst))
      |-> (carry == (((up_down == 1'b0) && ($past(q) == 4'hF)) ||
                     ((up_down == 1'b1) && ($past(q) == 4'd0))))
  );

  // No spurious carry when last q was mid-range (1..14).
  check_no_carry_midrange: assert property (
    @(posedge clk) disable iff (rst)
      (!$past(rst) && ($past(q) != 4'd0) && ($past(q) != 4'hF))
      |-> (carry == 1'b0)
  );

  // If carry is 1 in up mode, last q was 15 and q wrapped to 0.
  check_carry_only_on_up_wrap: assert property (
    @(posedge clk) disable iff (rst)
      (!$past(rst) && (up_down == 1'b0) && (carry == 1'b1))
      |-> ($past(q) == 4'hF) && (q == 4'd0)
  );

  // If carry is 1 in down mode, last q was 0 and q wrapped to 15.
  check_carry_only_on_down_wrap: assert property (
    @(posedge clk) disable iff (rst)
      (!$past(rst) && (up_down == 1'b1) && (carry == 1'b1))
      |-> ($past(q) == 4'd0) && (q == 4'hF)
  );

endmodule