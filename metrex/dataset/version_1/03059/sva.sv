// Assertions and coverage for GrayCounter
// Bind these to the DUT; concise but checks key functionality thoroughly.

module GrayCounter_sva #(
  parameter int unsigned CLK_DIV = 17_000_000
)(
  input  logic              clk,
  input  logic              rst,
  input  logic              stop,
  input  logic              incdec,
  input  logic [7:0]        gray,
  input  logic [7:0]        normal,
  input  logic [31:0]       clkDiv,   // internal
  input  logic [7:0]        curNum,   // internal
  input  logic [7:0]        curGray   // internal
);

  default clocking cb @(posedge clk); endclocking

  // 1) Synchronous reset drives known state next cycle
  assert property (@(posedge clk) rst |=> (clkDiv == 32'd0 && curNum == 8'd0));

  // 2) clkDiv never exceeds threshold (outside reset)
  assert property (disable iff (rst) clkDiv <= CLK_DIV);

  // 3) stop holds state (clkDiv and curNum) across cycles
  assert property (disable iff (rst)
    stop && $past(!rst) |=> (clkDiv == $past(clkDiv)) && (curNum == $past(curNum))
  );

  // 4) Free-running divider increments when not stopping and not hitting threshold
  assert property (disable iff (rst)
    !stop && $past(!rst) && ($past(clkDiv) != (CLK_DIV-1))
    |=> (clkDiv == $past(clkDiv) + 32'd1) && (curNum == $past(curNum))
  );

  // 5) At tick (when $past(clkDiv)==CLK_DIV-1 and not stopping), divider resets and curNum +/- 1 (mod 256)
  assert property (disable iff (rst)
    !stop && $past(!rst) && ($past(clkDiv) == (CLK_DIV-1))
    |=> (clkDiv == 32'd0) &&
        (curNum == ($past(curNum) + ($past(incdec) ? 8'h01 : 8'hFF)))
  );

  // 6) gray is always the Gray-code of PRIOR cycle's normal (1-cycle latency)
  assert property (disable iff (rst)
    $past(!rst) |-> (gray == ($past(normal) ^ ($past(normal) >> 1)))
  );

  // 7) Structural sanity: outputs mirror internals
  assert property (normal == curNum);
  assert property (gray   == curGray);

  // 8) No X on primary IO/outputs when out of reset
  assert property (disable iff (rst) !$isunknown({stop,incdec,gray,normal}));

  // ---------------- Coverage ----------------

  // A tick happens when the previous clkDiv was CLK_DIV-1 and not stopping
  sequence tick_s;
    !stop && $past(!rst) && ($past(clkDiv) == (CLK_DIV-1));
  endsequence

  // Cover increment tick
  cover property (disable iff (rst)
    tick_s && $past(incdec) |=> (curNum == ($past(curNum)+8'h01))
  );

  // Cover decrement tick
  cover property (disable iff (rst)
    tick_s && !$past(incdec) |=> (curNum == ($past(curNum)+8'hFF))
  );

  // Cover wrap-around on increment (FF -> 00)
  cover property (disable iff (rst)
    tick_s && $past(incdec) && ($past(curNum)==8'hFF) |=> (curNum==8'h00)
  );

  // Cover wrap-around on decrement (00 -> FF)
  cover property (disable iff (rst)
    tick_s && !$past(incdec) && ($past(curNum)==8'h00) |=> (curNum==8'hFF)
  );

  // Cover a multi-cycle stop hold interval
  cover property (disable iff (rst)
    $rose(stop) ##1 stop[*3] ##1 $fell(stop)
  );

endmodule

// Example bind (place in a separate file or a testbench):
// bind GrayCounter GrayCounter_sva #(.CLK_DIV(CLK_DIV)) gc_sva (
//   .clk(clk), .rst(rst), .stop(stop), .incdec(incdec),
//   .gray(gray), .normal(normal),
//   .clkDiv(clkDiv), .curNum(curNum), .curGray(curGray)
// );