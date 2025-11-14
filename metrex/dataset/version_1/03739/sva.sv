// SVA for spi. Bind to the DUT to check protocol, timing, and data moves.
// Focused, high-signal-to-noise assertions with essential coverage.

module spi_sva (
  input  logic         clk,
  input  logic         resn,
  input  logic         trig,
  input  logic         done,
  input  logic [15:0]  rdData,
  input  logic [15:0]  wrData,
  input  logic         SCLK,
  input  logic         SS,
  input  logic         MOSI,
  input  logic         MISO,
  input  logic [3:0]   state,
  input  logic [15:0]  bitCount,
  input  logic [15:0]  clkCounter
);

  // Simple tie-off check
  assert property (@(posedge clk) done == SS);

  // SCLK generation: changes at clk edge only when counter hits 33
  assert property (@(posedge clk)
    (SCLK != $past(SCLK)) |-> ($past(clkCounter) == 16'd33)
  );

  // Reset effects (as observed on any SCLK edge)
  assert property (@(posedge SCLK or negedge SCLK)
    !resn |-> (SS==1 && MOSI==0 && state==0 && bitCount==0)
  );

  // Active transfer implies SS low
  assert property (@(posedge SCLK or negedge SCLK) disable iff (!resn)
    (state==1) |-> SS==0
  );

  // Start of frame: SS falling only from idle, on SCLK low, and initializes state/bitCount
  assert property (@(posedge SCLK or negedge SCLK) disable iff (!resn)
    $fell(SS) |-> ($past(SCLK)==0 && $past(state)==0 && $past(trig)) &&
                 (state==1 && bitCount==15)
  );

  // End of frame: SS rises after SCLK high; returns to idle state, clears outputs
  assert property (@(posedge SCLK or negedge SCLK) disable iff (!resn)
    $rose(SS) |-> ($past(SCLK)==1) && (state==0 && MOSI==0 && bitCount==0)
  );

  // While active, bitCount stays in-range
  assert property (@(posedge SCLK or negedge SCLK) disable iff (!resn)
    (SS==0 && state==1) |-> (bitCount inside {[0:15]})
  );

  // bitCount decrements by 1 on each SCLK falling edge while active (until last bit)
  assert property (@(posedge SCLK or negedge SCLK) disable iff (!resn)
    ($fell(SCLK) && SS==0 && state==1 && bitCount>0) |-> ##2
      (SS==0 && state==1 && bitCount == $past(bitCount,2)-1)
  );

  // When last bit reached (bitCount==0 on SCLK fall), SS must deassert on next SCLK edge
  assert property (@(posedge SCLK or negedge SCLK) disable iff (!resn)
    ($fell(SCLK) && SS==0 && state==1 && bitCount==0) |-> ##1 (SS==1 && state==0)
  );

  // MOSI stable on SCLK high during active transfer (Mode 0 behavior inside state 1)
  assert property (@(posedge SCLK) disable iff (!resn)
    (SS==0 && state==1) |-> $stable(MOSI)
  );

  // MOSI driven from wrData at SCLK falling edges (except the terminal fall)
  assert property (@(negedge SCLK) disable iff (!resn)
    (SS==0 && state==1 && bitCount!=0) |-> ##1 (MOSI == wrData[$past(bitCount)])
  );

  // rdData bit sampling at SCLK rising edges
  assert property (@(posedge SCLK) disable iff (!resn)
    (SS==0 && state==1) |-> ##1 (rdData[$past(bitCount)] == $past(MISO))
  );

  // Optional: no X on primary SPI pins when out of reset
  assert property (@(posedge clk) disable iff (!resn)
    !$isunknown({SCLK,SS,MOSI})
  );

  // Coverage: observe a full 16-bit transfer from SS fall to SS rise
  cover property (@(posedge SCLK) disable iff (!resn)
    $fell(SS) ##1 (state==1 && bitCount==15) ##[1:$]
    ($rose(SCLK) && SS==0 && state==1 && bitCount==0) ##1 $rose(SS)
  );

endmodule

// Bind example (connect internal regs explicitly)
bind spi spi_sva u_spi_sva (
  .clk        (clk),
  .resn       (resn),
  .trig       (trig),
  .done       (done),
  .rdData     (rdData),
  .wrData     (wrData),
  .SCLK       (SCLK),
  .SS         (SS),
  .MOSI       (MOSI),
  .MISO       (MISO),
  .state      (state),
  .bitCount   (bitCount),
  .clkCounter (clkCounter)
);