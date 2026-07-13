module bcd_counter_sva (
  input logic clk,
  input logic reset,
  input logic [2:0] enable,
  input logic [9:0] q
);

  // Synchronous reset drives q to zero on the same cycle.
  reset_clears_q: assert property (
    @(posedge clk) reset |=> (q == 10'd0)
  );

  // Digits stay within encoded ranges when not in reset.
  digits_in_range: assert property (
    @(posedge clk) disable iff (reset)
      (q[9:6] <= 4'd9) && (q[5:2] <= 4'd9) && (q[1:0] <= 2'd3)
  );

  // When enable[2] was LOW last cycle, q holds its value.
  hold_when_prev_en2_low: assert property (
    @(posedge clk) disable iff (reset || $past(reset))
      (!$past(enable[2])) |=> (q == $past(q))
  );

  // If last cycle enable[2]=1 and q[9:6]!=9, increment only the top digit.
  inc_high_nibble_no_wrap: assert property (
    @(posedge clk) disable iff (reset || $past(reset))
      ($past(enable[2]) && ($past(q[9:6]) != 4'd9)) |=> 
        ( (q[9:6] == $past(q[9:6]) + 4'd1) &&
          (q[5:2] == $past(q[5:2])) &&
          (q[1:0] == $past(q[1:0])) )
  );

  // If last cycle q[9:6]==9 with enable[2]=1 and enable[1]=0, wrap top and hold others.
  wrap_high_no_mid_enable: assert property (
    @(posedge clk) disable iff (reset || $past(reset))
      ($past(enable[2]) && ($past(q[9:6]) == 4'd9) && (!$past(enable[1]))) |=> 
        ( (q[9:6] == 4'd0) &&
          (q[5:2] == $past(q[5:2])) &&
          (q[1:0] == $past(q[1:0])) )
  );

  // If last cycle top wrapped and enable[1]=1 with mid!=9, increment mid and hold low.
  wrap_high_mid_inc: assert property (
    @(posedge clk) disable iff (reset || $past(reset))
      ($past(enable[2]) && ($past(q[9:6]) == 4'd9) && $past(enable[1]) && ($past(q[5:2]) != 4'd9)) |=> 
        ( (q[9:6] == 4'd0) &&
          (q[5:2] == $past(q[5:2]) + 4'd1) &&
          (q[1:0] == $past(q[1:0])) )
  );

  // If last cycle top wrapped, mid==9, and enable[0]=0, wrap mid and hold low.
  wrap_high_mid_wrap_no_low: assert property (
    @(posedge clk) disable iff (reset || $past(reset))
      ($past(enable[2]) && ($past(q[9:6]) == 4'd9) && $past(enable[1]) && ($past(q[5:2]) == 4'd9) && (!$past(enable[0]))) |=> 
        ( (q[9:6] == 4'd0) &&
          (q[5:2] == 4'd0) &&
          (q[1:0] == $past(q[1:0])) )
  );

  // If last cycle both higher digits wrapped and low!=3 with enable[0]=1, increment low.
  wrap_high_mid_wrap_low_inc: assert property (
    @(posedge clk) disable iff (reset || $past(reset))
      ($past(enable[2]) && ($past(q[9:6]) == 4'd9) && $past(enable[1]) && ($past(q[5:2]) == 4'd9) && $past(enable[0]) && ($past(q[1:0]) != 2'd3)) |=> 
        ( (q[9:6] == 4'd0) &&
          (q[5:2] == 4'd0) &&
          (q[1:0] == $past(q[1:0]) + 2'd1) )
  );

  // If last cycle both higher digits wrapped and low==3 with enable[0]=1, wrap low to 0.
  wrap_high_mid_wrap_low_wrap: assert property (
    @(posedge clk) disable iff (reset || $past(reset))
      ($past(enable[2]) && ($past(q[9:6]) == 4'd9) && $past(enable[1]) && ($past(q[5:2]) == 4'd9) && $past(enable[0]) && ($past(q[1:0]) == 2'd3)) |=> 
        ( (q[9:6] == 4'd0) &&
          (q[5:2] == 4'd0) &&
          (q[1:0] == 2'd0) )
  );

  // Top digit changes only if enable[2] was HIGH last cycle.
  change_high_requires_en2: assert property (
    @(posedge clk) disable iff (reset || $past(reset))
      $changed(q[9:6]) |=> $past(enable[2])
  );

  // Mid digit changes only if last cycle had enable[2]=1, top==9, and enable[1]=1.
  change_mid_requires_chain: assert property (
    @(posedge clk) disable iff (reset || $past(reset))
      $changed(q[5:2]) |=> ($past(enable[2]) && ($past(q[9:6]) == 4'd9) && $past(enable[1]))
  );

  // Low digit changes only if last cycle had full carry chain and enable[0]=1.
  change_low_requires_full_chain: assert property (
    @(posedge clk) disable iff (reset || $past(reset))
      $changed(q[1:0]) |=> ($past(enable[2]) && ($past(q[9:6]) == 4'd9) && $past(enable[1]) && ($past(q[5:2]) == 4'd9) && $past(enable[0]))
  );

endmodule