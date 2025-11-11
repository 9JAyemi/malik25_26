// SVA for RCB_FRL_count_to_128
module RCB_FRL_count_to_128_sva(
  input  logic        clk,
  input  logic        rst,
  input  logic        count,
  input  logic        ud,
  input  logic [6:0]  counter_value
);
  default clocking cb @(posedge clk); endclocking

  // No X/Z on important signals
  assert property (! $isunknown({rst,count,ud,counter_value}));

  // Asynchronous reset: immediate to 0 on rst rise
  assert property (@(posedge rst) counter_value == 7'h00);
  // While in reset, value held at 0 on every clk
  assert property (rst |-> counter_value == 7'h00);

  // Next-state functional checks (gated from previous cycle not in reset)
  assert property (disable iff (rst)
                   $past(!rst && {count,ud}==2'b00) |-> counter_value == 7'd0);

  assert property (disable iff (rst)
                   $past(!rst && {count,ud}==2'b01) |-> counter_value == $past(counter_value));

  assert property (disable iff (rst)
                   $past(!rst && {count,ud}==2'b10) |-> counter_value == ($past(counter_value) - 7'd1));

  assert property (disable iff (rst)
                   $past(!rst && {count,ud}==2'b11) |-> counter_value == ($past(counter_value) + 7'd1));

  // Explicit wrap-around checks
  assert property (disable iff (rst)
                   $past(!rst && {count,ud}==2'b11 && $past(counter_value)==7'd127) |-> counter_value == 7'd0);

  assert property (disable iff (rst)
                   $past(!rst && {count,ud}==2'b10 && $past(counter_value)==7'd0) |-> counter_value == 7'd127);

  // Coverage: see each mode and both wraps after coming out of reset
  cover property (rst ##1 !rst);
  cover property (disable iff (rst) {count,ud}==2'b00);
  cover property (disable iff (rst) {count,ud}==2'b01);
  cover property (disable iff (rst) {count,ud}==2'b10);
  cover property (disable iff (rst) {count,ud}==2'b11);
  cover property (disable iff (rst)
                  $past({count,ud}==2'b11 && $past(counter_value)==7'd127) ##1 counter_value==7'd0);
  cover property (disable iff (rst)
                  $past({count,ud}==2'b10 && $past(counter_value)==7'd0)   ##1 counter_value==7'd127);

endmodule

// Bind into DUT
bind RCB_FRL_count_to_128 RCB_FRL_count_to_128_sva u_RCB_FRL_count_to_128_sva(
  .clk(clk),
  .rst(rst),
  .count(count),
  .ud(ud),
  .counter_value(counter_value)
);