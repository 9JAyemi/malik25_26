// SVA for clk_div
module clk_div_sva (
  input logic        clk,
  input logic        rst,
  input logic        SW2,
  input logic [31:0] clkdiv,
  input logic        Clk_CPU
);

  default clocking cb @(posedge clk); endclocking

  // Reset forces zeros
  ap_rst_zero: assert property (rst |-> (clkdiv == 32'd0 && Clk_CPU == 1'b0));

  // Counter increments by 1 every clk when not in reset (wraps naturally)
  ap_inc:       assert property (disable iff (rst) clkdiv == $past(clkdiv) + 32'd1);

  // First non-reset cycle after reset -> counter goes to 1
  ap_first_inc: assert property ($past(rst) && !rst |-> clkdiv == 32'd1);

  // Correct muxing of Clk_CPU
  ap_sel1:      assert property (SW2  |-> Clk_CPU == clkdiv[22]);
  ap_sel0:      assert property (!SW2 |-> Clk_CPU == clkdiv[1]);

  // No X/Z on key signals after reset
  ap_no_x:      assert property (disable iff (rst) !$isunknown({SW2, clkdiv, Clk_CPU}));

  // Coverage
  cp_reset_seq:  cover property ($rose(rst) ##[1:$] $fell(rst));
  cp_mode0:      cover property (disable iff (rst) SW2 == 1'b0);
  cp_mode1:      cover property (disable iff (rst) SW2 == 1'b1);
  cp_sw2_switch: cover property (disable iff (rst) $changed(SW2));
  cp_toggle0:    cover property (disable iff (rst) (SW2==1'b0) ##1 $changed(Clk_CPU));
  cp_toggle1:    cover property (disable iff (rst) (SW2==1'b1) ##1 $changed(Clk_CPU));

endmodule

// Bind into DUT
bind clk_div clk_div_sva u_clk_div_sva(.clk(clk), .rst(rst), .SW2(SW2), .clkdiv(clkdiv), .Clk_CPU(Clk_CPU));