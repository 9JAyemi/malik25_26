// SVA for fifo496: concise, high-quality checks and coverage.
// Bind these assertions to the DUT; no DUT/testbench edits needed beyond bind.

module fifo496_sva #(parameter int WIDTH = 8)(
  input  logic                 clk,
  input  logic                 wen,
  input  logic [WIDTH-1:0]     din,
  input  logic [WIDTH-1:0]     dout,
  input  logic [WIDTH-1:0]     buff1,
  input  logic [WIDTH-1:0]     buff2
);
  default clocking cb @(posedge clk); endclocking

  // Hold behavior on !wen (skip first cycle to avoid $past issues)
  assert property (1'b1 |=> !wen |-> $stable({buff1,buff2,dout}));

  // Stage updates on wen (non-overlapping to account for NBA update timing)
  assert property (wen |=> buff1 == $past(din));
  assert property (wen |=> buff2 == $past(buff1));
  assert property (wen |=> dout  == $past(buff2));

  // No unintended changes without a prior wen
  assert property (1'b1 |=> $changed(buff1) |-> $past(wen));
  assert property (1'b1 |=> $changed(buff2) |-> $past(wen));
  assert property (1'b1 |=> $changed(dout)  |-> $past(wen));

  // Latency with three consecutive writes
  assert property (wen[*3] |=> dout == $past(din,3));

  // General stall-aware latency: value appears after two subsequent wen pulses (total three)
  sequence next_wen; !wen [*0:$] ##1 wen; endsequence
  property stall_aware_latency;
    int d;
    (wen, d = din) |-> next_wen ##1 next_wen ##1 (dout == d);
  endproperty
  assert property (stall_aware_latency);

  // X/validity checks (skip first cycle)
  assert property (1'b1 |=> !$isunknown(wen));
  assert property (wen |-> !$isunknown(din));
  assert property (1'b1 |=> $changed(dout) |-> !$isunknown(dout));

  // Coverage
  cover property (wen);                     // see any write
  cover property (wen[*3]);                 // see 3 consecutive writes
  cover property (stall_aware_latency);     // see stalled propagation
  cover property (!wen[*5]);                // see long idle
endmodule

// Bind into the DUT (tools typically allow parameter passthrough this way)
bind fifo496 fifo496_sva #(.WIDTH(WIDTH)) fifo496_sva_i (
  .clk   (clk),
  .wen   (wen),
  .din   (din),
  .dout  (dout),
  .buff1 (buff1),
  .buff2 (buff2)
);