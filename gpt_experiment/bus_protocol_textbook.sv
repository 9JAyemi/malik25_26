`timescale 1ns/1ps
`default_nettype none
// ============================================================
// LAB5 : bus_protocol_property.sv  (Answers converted to SVA)
// ============================================================

module bus_protocol_property (
  input  logic       clk,
  input  logic       reset,   // active-high
  input  logic       dValid,
  input  logic       dAck,
  input  logic [7:0] data
);

  default clocking cb @(posedge clk); endclocking
  `define DISABLE_RST disable iff (reset)

  /*------------------------------------------------------------
   CHECK #1
   Once dValid goes high it must stay high for min 2 / max 4
   clocks, then de-assert the very next clock.
  ------------------------------------------------------------*/
`ifdef check1
  property checkValid;
    @(cb) `DISABLE_RST
      $rose(dValid) |=>  (dValid)[*2:4] ##1 $fell(dValid);
  endproperty
  assert property (checkValid)
    else $display($stime,,,"checkValid FAIL");
`endif

  /*------------------------------------------------------------
   CHECK #2
   After dValid goes high, data must be known and remain stable
   until dAck goes high.
  ------------------------------------------------------------*/
`ifdef check2
  property checkdataValid;
    @(cb) `DISABLE_RST
      $rose(dValid) |=> ((!$isunknown(data) && $stable(data)))[*1:$] ##0 $rose(dAck);
  endproperty
  assert property (checkdataValid)
    else $display($stime,,,"checkdataValid FAIL");
`endif

  /*------------------------------------------------------------
   CHECK #3
   dAck rising signifies data accepted; master must de-assert
   dValid one clock after dAck rises.
   Since data must be valid 2..4 cycles, dAck cannot rise
   earlier than 1 cycle after dValid rises and must not be
   delayed more than 3 cycles.
  ------------------------------------------------------------*/
`ifdef check3
  property checkdAck;
    @(cb) `DISABLE_RST
      $rose(dValid) |=> (dValid && !dAck)[*1:3] ##1 $rose(dAck) ##1 $fell(dValid);
  endproperty
  assert property (checkdAck)
    else $display($stime,,,"checkdAck FAIL");
`endif

endmodule

// Optional bind:
// bind bus_protocol bus_protocol_property u_bus_protocol_property (.*);

`default_nettype wire
