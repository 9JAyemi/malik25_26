// SVA for previous_data
module previous_data_sva #(parameter WIDTH=32)
(
  input logic              clk,
  input logic              rst,
  input logic [WIDTH-1:0]  data_in,
  input logic [WIDTH-1:0]  data_out
);

  default clocking cb @(posedge clk); endclocking

  // Known/clean control and outputs
  assert property (!$isunknown(rst)) else $error("rst is X/Z");
  assert property (cb disable iff (rst) !$isunknown(data_out)) else $error("data_out X/Z when not in reset");

  // Synchronous behavior: registered pass-through (one-cycle latency)
  assert property (cb disable iff (rst) (!$past(rst)) |-> data_out == $past(data_in))
    else $error("data_out != previous-cycle data_in");

  // While in reset at a clock edge, output is 0
  assert property (cb rst |-> data_out == '0)
    else $error("data_out not 0 while rst=1 at clk");

  // Asynchronous reset takes effect immediately
  assert property (@(posedge rst) ##0 (data_out == '0))
    else $error("data_out not driven 0 on rst assertion");

  // Stay 0 for entire duration of rst
  assert property ($rose(rst) |-> (data_out == '0 throughout rst))
    else $error("data_out left 0 while rst held high");

  // After rst deasserts, hold 0 until the next posedge clk
  assert property (@(negedge rst) (data_out == '0 and (data_out == '0 until_with posedge clk)))
    else $error("data_out changed before first clk after rst deassert");

  // data_out only changes on clk or rst events
  assert property ($changed(data_out) |-> ($rose(clk) or $rose(rst)))
    else $error("data_out changed without clk or rst edge");

  // Coverage
  cover property (cb rst ##1 !rst ##1 !rst ##1 (data_in != '0) ##1 (data_out == $past(data_in)));
  cover property (cb disable iff (rst) (data_in != $past(data_in)) ##1 (data_out == $past(data_in)));

endmodule

// Bind into DUT
bind previous_data previous_data_sva #(.WIDTH(32)) u_previous_data_sva
(
  .clk      (clk),
  .rst      (rst),
  .data_in  (data_in),
  .data_out (data_out)
);