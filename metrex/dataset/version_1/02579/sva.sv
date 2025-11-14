// SVA for SPI module
// Bind once in your testbench: bind SPI spi_sva #( .ClkPeriod(ClkPeriod) ) spi_sva_i (.* , .ClkStatus(ClkStatus), .Counter(Counter));

module spi_sva
#(parameter real ClkPeriod = 20.0)
(
  input  logic       Clk,
  input  logic       MOSI,
  input  logic       MISO,
  input  logic       SCLK,
  input  logic       SCE,
  input  logic       Enable,
  input  logic       Speed,
  input  logic [7:0] SendData,
  input  logic       SendReq,
  input  logic       SendAck,
  input  logic [7:0] RecvData,
  input  logic       RecvAdv,
  input  logic       RecvAck,
  input  int         ClkStatus,
  input  int         Counter
);

  default clocking cb @(posedge Clk); endclocking

  // Clock/status invariants (skip time 0)
  assert property ( $past(1'b1) |-> (ClkStatus inside {1,2}) );
  assert property ( $past(1'b1) |-> ((ClkStatus==1) |-> SCLK) );
  assert property ( $past(1'b1) |-> ((ClkStatus==2) |-> !SCLK) );

  // CS behavior
  assert property ( !Enable |-> SCE );                // Disabled => CS high
  assert property ( $fell(SCE) |-> Enable );          // CS can only deassert when enabled
  assert property ( SCE |-> (MOSI && !RecvAdv) );     // Idle while CS high

  // SPI mode-0 alignment
  assert property ( $rose(SCLK) |-> $stable(MOSI) until_with $fell(SCLK) ); // MOSI stable while SCLK high
  assert property ( $changed(MOSI) |-> $fell(SCLK) );                       // MOSI only updates on SCLK falling
  assert property ( RecvAdv |-> (!SCE && $rose(SCLK)) );                    // Data-available only on SCLK rise with CS low

  // Receive handshake
  property p_recv_hold;
    RecvAdv |-> (RecvAdv && $stable(RecvData)) until RecvAck;              // Hold data stable until ack
  endproperty
  assert property (p_recv_hold);

  // Ack clears RecvAdv on next cycle if no concurrent new-recv event
  assert property ( RecvAck && !($rose(SCLK) && !SCE && (Counter==0)) |=> !RecvAdv );

  // Optional sanity on SCLK toggling (no double rises/falls)
  assert property ( $rose(SCLK) |=> !($rose(SCLK)) until $fell(SCLK) );
  assert property ( $fell(SCLK) |=> !($fell(SCLK)) until $rose(SCLK) );

  // ------------------
  // Functional coverage
  // ------------------

  // Cover both speeds active on SCLK
  cover property ( !SCE && !Speed ##1 $rose(SCLK) );
  cover property ( !SCE &&  Speed ##1 $rose(SCLK) );

  // Cover a complete received byte (8 SCLK rises) and data-available pulse
  cover property ( !SCE ##1 $rose(SCLK)[*8] ##1 RecvAdv );

  // Cover two consecutive bytes while CS stays low
  cover property ( !SCE ##1 $rose(SCLK)[*8] ##1 RecvAdv ##1 $rose(SCLK)[*8] ##1 RecvAdv );

  // Cover Send request being taken at start-of-frame (CS drop)
  cover property ( $fell(SCE) && SendReq );

  // Cover RecvAdv -> RecvAck handshake
  cover property ( RecvAdv ##[1:32] RecvAck );

endmodule

bind SPI spi_sva #( .ClkPeriod(ClkPeriod) ) spi_sva_i (.* , .ClkStatus(ClkStatus), .Counter(Counter));