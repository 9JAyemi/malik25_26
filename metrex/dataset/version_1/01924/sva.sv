// SVA for counter
module counter_sva(input logic clk, rst, en, input logic [3:0] out);

  // Track $past validity
  bit past_valid;
  initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;

  // Reset behavior
  a_rst_clears: assert property (@(posedge clk) rst |=> out == 4'd0);
  a_rst_holds:  assert property (@(posedge clk) past_valid && $past(rst) && rst |-> out == 4'd0);

  // Known value when not in reset
  a_no_x_post_rst: assert property (@(posedge clk) !rst |-> !$isunknown(out));

  // Functional behavior
  a_inc:  assert property (@(posedge clk) past_valid && !rst && en  |=> out == (($past(out)+1) & 4'hF));
  a_hold: assert property (@(posedge clk) past_valid && !rst && !en |=> out == $past(out));

  // Coverage
  c_reset: cover property (@(posedge clk) rst ##1 out == 4'd0);
  c_inc:   cover property (@(posedge clk) past_valid && !rst && en ##1 out == (($past(out)+1) & 4'hF));
  c_hold:  cover property (@(posedge clk) past_valid && !rst && !en ##1 out == $past(out));
  c_wrap:  cover property (@(posedge clk) !rst && en && (out==4'hF) ##1 out==4'h0);
  c_seq:   cover property (@(posedge clk) rst ##1 !rst ##1 en [*3]);

endmodule

bind counter counter_sva sva_i (.clk(clk), .rst(rst), .en(en), .out(out));