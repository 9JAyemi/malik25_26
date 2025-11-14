// SystemVerilog Assertions (SVA) for the provided modules
// Focused, concise, high-quality checks + useful coverage

// ===================== dly_signal =====================
module dly_signal_sva #(parameter int WIDTH = 1)
(
  input logic                   clk,
  input logic [WIDTH-1:0]       indata,
  input logic [WIDTH-1:0]       outdata
);
  default clocking @(posedge clk); endclocking

  // Guard first-cycle $past
  logic past_valid;
  initial past_valid = 0;
  always @(posedge clk) past_valid <= 1;

  // 1-cycle functional delay
  assert property (past_valid |-> outdata == $past(indata));

  // No X on out once input history is known
  assert property (past_valid && !$isunknown($past(indata)) |-> !$isunknown(outdata));

  // Coverage: change propagates by 1 cycle
  cover property ($changed(indata) ##1 outdata == $past(indata));
endmodule

bind dly_signal dly_signal_sva #(.WIDTH(WIDTH)) (.clk(clk), .indata(indata), .outdata(outdata));


// ===================== pipeline_stall =====================
module pipeline_stall_sva #(parameter int WIDTH = 1, parameter int DELAY = 1)
(
  input  logic                          clk,
  input  logic                          reset,
  input  logic [WIDTH-1:0]              datain,
  input  logic [WIDTH-1:0]              dataout,
  input  logic [(WIDTH*DELAY)-1:0]      dly_datain
);
  default clocking @(posedge clk); endclocking

  // Static parameter sanity
  initial begin
    assert (WIDTH >= 1);
    assert (DELAY >= 1);
  end

  // Asynchronous reset clears state immediately
  always @(posedge reset) begin
    assert (dly_datain == '0);
    assert (dataout   == '0);
  end

  // Shift-register behavior when not in reset
  assert property (disable iff (reset)
                   dly_datain == {$past(dly_datain), $past(datain)});

  // Functional DELAY: output equals input delayed by DELAY when reset low for DELAY cycles
  assert property (disable iff (reset)
                   (!reset[*DELAY]) |-> dataout == $past(datain, DELAY));

  // No X once the pipeline window is valid and input history known
  assert property (disable iff (reset)
                   (!reset[*DELAY] && !$isunknown($past(datain, DELAY))) |-> !$isunknown(dataout));

  // Coverage: a change on input emerges after DELAY cycles
  cover property (disable iff (reset)
                  $changed(datain) ##DELAY (dataout == $past(datain, DELAY)));

  // Coverage: reset clears output
  cover property (@(posedge reset) 1'b1 ##0 dataout == '0);
endmodule

bind pipeline_stall pipeline_stall_sva #(.WIDTH(WIDTH), .DELAY(DELAY))
(
  .clk(clk), .reset(reset), .datain(datain), .dataout(dataout), .dly_datain(dly_datain)
);


// ===================== full_synchronizer =====================
module full_synchronizer_sva #(parameter int WIDTH = 1)
(
  input logic                   clk,
  input logic                   reset,
  input logic [WIDTH-1:0]       datain,
  input logic [WIDTH-1:0]       dataout
);
  default clocking @(posedge clk); endclocking

  initial assert (WIDTH >= 1);

  // Asynch reset drives output low immediately (through internal pipeline)
  always @(posedge reset) assert (dataout == '0);

  // 2-cycle synchronizer functional behavior when reset low for 2 cycles
  assert property (disable iff (reset)
                   (!reset[*2]) |-> dataout == $past(datain, 2));

  // Coverage: propagation over 2 cycles
  cover property (disable iff (reset)
                  $changed(datain) ##2 (dataout == $past(datain, 2)));
  // Coverage: explicit 0->1 propagation on bit 0
  cover property (disable iff (reset)
                  $rose(datain[0]) ##2 (dataout[0] && $past(datain[0],2)));
endmodule

bind full_synchronizer full_synchronizer_sva #(.WIDTH(WIDTH))
  (.clk(clk), .reset(reset), .datain(datain), .dataout(dataout));


// ===================== reset_sync =====================
module reset_sync_sva
(
  input  logic       clk,
  input  logic       hardreset,
  input  logic [3:0] reset_reg,
  input  logic       reset
);
  default clocking @(posedge clk); endclocking

  // Async load on hardreset
  always @(posedge hardreset) begin
    assert (reset_reg == 4'hF);
    assert (reset     == 1'b1);
  end

  // While hardreset is asserted, reset must be high
  assert property (hardreset |-> reset);

  // After 4 cycles of hardreset low, reset must be low
  assert property ((!hardreset[*4]) |-> !reset);

  // Precise deassertion: after a sampled rise of hardreset, hold 4 cycles high then low
  assert property ($rose(hardreset) |-> reset[*4] ##1 !reset);

  // Monotonic behavior after deassertion: once low, stays low until next hardreset
  assert property ((!reset && !hardreset) |=> (!reset && !hardreset)[*0:$] until_with $rose(hardreset));

  // Shift-left with zero when not in hardreset
  assert property (disable iff (hardreset)
                   reset_reg == {$past(reset_reg[2:0]), 1'b0});

  // Coverage: typical sequence (assert -> 4 clocks low -> deassert)
  cover property ($rose(hardreset) ##1 !hardreset[*4] ##1 !reset);
  // Coverage: observe reset falling edge
  cover property ($fell(reset));
endmodule

bind reset_sync reset_sync_sva (.clk(clk), .hardreset(hardreset), .reset_reg(reset_reg), .reset(reset));