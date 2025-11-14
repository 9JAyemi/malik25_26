// SVA for value_buffer: concise functional checks + targeted coverage
// Bindable checker module
module value_buffer_sva #(parameter int W=64) (
  input logic                    clk,
  input logic [W-1:0]            c0_in, c1_in, c2_in, c3_in,
  input logic [W-1:0]            c0_up, c1_up, c2_up, c3_up,
  input logic [W-1:0]            c0_down, c1_down, c2_down, c3_down
);

  default clocking cb @(posedge clk); endclocking

  logic past_valid;
  initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;

  // One-cycle latency down path
  assert property (past_valid |-> (c0_down == $past(c0_in)));
  assert property (past_valid |-> (c1_down == $past(c1_in)));
  assert property (past_valid |-> (c2_down == $past(c2_in)));
  assert property (past_valid |-> (c3_down == $past(c3_in)));

  // Up path: three registered lanes and one bypass
  assert property (past_valid |-> (c0_up == $past(c1_in)));
  assert property (past_valid |-> (c1_up == $past(c2_in)));
  assert property (past_valid |-> (c2_up == $past(c3_in)));
  assert property (c3_up == c0_in);  // zero-latency bypass

  // Targeted functional coverage
  cover property (past_valid && $changed(c0_in) ##1 (c0_down == $past(c0_in)));
  cover property (past_valid && $changed(c1_in) ##1 (c1_down == $past(c1_in)));
  cover property (past_valid && $changed(c2_in) ##1 (c2_down == $past(c2_in)));
  cover property (past_valid && $changed(c3_in) ##1 (c3_down == $past(c3_in)));

  cover property (past_valid && $changed(c1_in) ##1 (c0_up == $past(c1_in)));
  cover property (past_valid && $changed(c2_in) ##1 (c1_up == $past(c2_in)));
  cover property (past_valid && $changed(c3_in) ##1 (c2_up == $past(c3_in)));

  cover property ($changed(c0_in) && (c3_up == c0_in)); // bypass exercised

endmodule

// Bind into DUT
bind value_buffer value_buffer_sva #(.W(64)) value_buffer_sva_i (
  .clk     (clk),
  .c0_in   (c0_in),   .c1_in   (c1_in),   .c2_in   (c2_in),   .c3_in   (c3_in),
  .c0_up   (c0_up),   .c1_up   (c1_up),   .c2_up   (c2_up),   .c3_up   (c3_up),
  .c0_down (c0_down), .c1_down (c1_down), .c2_down (c2_down), .c3_down (c3_down)
);