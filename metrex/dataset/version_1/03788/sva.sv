// SVA for sequence_detector
`ifndef SEQUENCE_DETECTOR_SVA
`define SEQUENCE_DETECTOR_SVA

module sequence_detector_sva (
  input logic clk,
  input logic reset,
  input logic in,
  input logic out,
  input logic [1:0] state
);
  localparam logic [1:0] START = 2'b00;
  localparam logic [1:0] FINAL = 2'b01;

  default clocking cb @(posedge clk); endclocking

  bit past_valid;
  always @(posedge clk) past_valid <= 1'b1;

  // Environment/sanity
  assume property (!$isunknown({reset,in}));
  assert property (!$isunknown({state,out}));
  assert property (state inside {START, FINAL});

  // Reset behavior (async and sync)
  assert property (@(posedge reset) ##0 (state==START && out==1'b0));
  assert property (reset |-> (state==START && out==1'b0));

  // Output mapping
  assert property (out == (state==FINAL));

  // Functional behavior: 1-cycle delay of input
  assert property (past_valid && !$past(reset) && !reset |-> state == ($past(in) ? FINAL : START));
  assert property (past_valid && !$past(reset) && !reset |-> out == $past(in));

  // Coverage
  cover property (disable iff (reset)) (state==START);
  cover property (disable iff (reset)) (state==FINAL);
  cover property (disable iff (reset)) (!in ##1 in ##1 !in);
  cover property (disable iff (reset)) (!out ##1 out ##1 !out);
  cover property (@(posedge reset) 1);

endmodule

// Bind into DUT
bind sequence_detector sequence_detector_sva sva_i (
  .clk(clk),
  .reset(reset),
  .in(in),
  .out(out),
  .state(state)
);

`endif