// SVA for barrel_shifter
// Focus: end-to-end correctness, pipeline sequencing, X-safety, and concise coverage

module barrel_shifter_sva (
  input  logic        clk,
  input  logic [3:0]  in,
  input  logic [1:0]  ctrl,
  input  logic [3:0]  out,
  input  logic [3:0]  stage1_out,
  input  logic [3:0]  stage2_out
);

  default clocking cb @(posedge clk); endclocking

  function automatic logic [3:0] shift4 (input logic [3:0] x, input logic [1:0] c);
    case (c)
      2'b00: shift4 = {x[2:0], 1'b0};  // <<1
      2'b01: shift4 = {x[1:0], 2'b0};  // <<2
      2'b10: shift4 = {1'b0, x[3:1]};  // >>1
      2'b11: shift4 = {2'b0, x[3:2]};  // >>2
    endcase
  endfunction

  // Past-valid trackers to avoid false failures at startup
  logic past1, past2;
  always @(posedge clk) begin
    past1 <= 1'b1;
    past2 <= past1;
  end

  // Sanity: inputs must not be X/Z once clocking starts
  assert property (past1 |-> !$isunknown(ctrl));
  assert property (past1 |-> !$isunknown(in));

  // Stage1 must implement the correct shift function at the sampling edge
  assert property (shift4(in, ctrl) == stage1_out);

  // Pipeline sequencing (catches race/ordering issues)
  assert property (past1 |-> stage2_out == $past(stage1_out));
  assert property (past2 |-> out        == $past(stage2_out));

  // End-to-end 2-cycle latency and correctness
  assert property (past2 |-> out == $past(shift4(in, ctrl), 2));

  // No X propagation after pipeline is primed
  assert property (past2 |-> !$isunknown(stage1_out) && !$isunknown(stage2_out) && !$isunknown(out));

  // Functional coverage: exercise all shift types and key edge patterns
  cover property (past2 && ctrl == 2'b00 && in == 4'b0001 && out == $past(shift4(in, ctrl), 2)); // <<1 from LSB
  cover property (past2 && ctrl == 2'b01 && in == 4'b0011 && out == $past(shift4(in, ctrl), 2)); // <<2
  cover property (past2 && ctrl == 2'b10 && in == 4'b1000 && out == $past(shift4(in, ctrl), 2)); // >>1 from MSB
  cover property (past2 && ctrl == 2'b11 && in == 4'b1100 && out == $past(shift4(in, ctrl), 2)); // >>2
  cover property (past2 && in == 4'b0000); // all zeros
  cover property (past2 && in == 4'b1111); // all ones
  cover property (past2 && $changed(in));
  cover property (past2 && $changed(ctrl));

endmodule

// Bind into the DUT
bind barrel_shifter barrel_shifter_sva u_barrel_shifter_sva (
  .clk        (clk),
  .in         (in),
  .ctrl       (ctrl),
  .out        (out),
  .stage1_out (stage1_out),
  .stage2_out (stage2_out)
);