// SVA for top_module
// Bind into DUT to access internals
bind top_module top_module_sva sva_i (
  .clk(clk),
  .reset(reset),
  .ena(ena),
  .in(in),
  .sel(sel),
  .counter(counter),
  .mux_output(mux_output),
  .select_input(select_input),
  .add_output(add_output),
  .out(out)
);

module top_module_sva (
  input clk,
  input reset,
  input ena,
  input [1023:0] in,
  input [7:0] sel,
  input [15:0] counter,
  input [7:0] mux_output,
  input [3:0] select_input,
  input [11:0] add_output,
  input [7:0] out
);

  default clocking cb @(posedge clk); endclocking

  // Basic X-checks (after reset low)
  assert property (!reset |-> !$isunknown({counter,mux_output,select_input,add_output,out})));

  // Synchronous reset behavior
  assert property (reset |=> counter == 16'd0);
  assert property ($past(reset) |-> counter == 16'd0);

  // Counter holds/increments
  assert property (!reset && !ena |=> counter == $past(counter));
  assert property (!reset && ena  |=> counter == $past(counter) + 16'd1);

  // Select input mapping and onehot0
  assert property (select_input == (4'b0001 << sel[2:0]));
  assert property ($onehot0(select_input));

  // Mux index in range and mux correctness
  let idx = (select_input * 12'd4);
  assert property (idx <= 12'd1020);
  assert property (mux_output == in[idx +: 4]);

  // Explicit behavior when sel[2:0] >= 4 (shift beyond width -> select_input==0 => idx==0)
  assert property (sel[2:0] >= 3'd4 |-> (select_input == 4'b0000 && mux_output == in[3:0]));

  // Adder sizing/truncation and output mapping
  assert property (add_output == (counter + mux_output)[11:0]);
  assert property (out == add_output[11:4]);

  // Coverage
  cover property (reset ##1 !reset);                                 // reset cycle seen
  cover property (!reset && ena ##1 counter == $past(counter)+1);    // increment occurs
  cover property (!reset && !ena ##1 counter == $past(counter));     // hold occurs
  cover property ($past(counter)==16'hFFFF && !reset && ena ##1 counter==16'h0000); // rollover

  cover property (sel[2:0]==3'd0 && select_input==4'b0001 && idx==12'd4);
  cover property (sel[2:0]==3'd1 && select_input==4'b0010 && idx==12'd8);
  cover property (sel[2:0]==3'd2 && select_input==4'b0100 && idx==12'd16);
  cover property (sel[2:0]==3'd3 && select_input==4'b1000 && idx==12'd32);
  cover property (sel[2:0]>=3'd4  && select_input==4'b0000 && idx==12'd0);

  // Exercise adder truncation affecting OUT (carry from low nibble into [11:4])
  cover property (!reset ##1 ((counter + mux_output)[3:0]==4'hF) ##1 out != $past(out));

endmodule