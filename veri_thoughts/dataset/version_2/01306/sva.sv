module pipeline_2_latch_sva(
  input logic clk, CinWire1, immBit1,
  input logic [31:0] abusWire1, bbusWire1, DselectWire1, immWire1,
  input logic [2:0] SWire1,
  input logic [1:0] lwSwFlag1,
  input logic CinWire2, immBit2,
  input logic [31:0] abusWire2, bbusWire2, DselectWire2, immWire2,
  input logic [2:0] SWire2,
  input logic [1:0] lwSwFlag2
);

  // abusWire2 equals abusWire1 from the previous clock.
  check_abus_pipeline: assert property (
    @(posedge clk) abusWire2 == $past(abusWire1)
  );

  // bbusWire2 equals bbusWire1 from the previous clock.
  check_bbus_pipeline: assert property (
    @(posedge clk) bbusWire2 == $past(bbusWire1)
  );

  // DselectWire2 equals DselectWire1 from the previous clock.
  check_Dselect_pipeline: assert property (
    @(posedge clk) DselectWire2 == $past(DselectWire1)
  );

  // immWire2 equals immWire1 from the previous clock.
  check_immWire_pipeline: assert property (
    @(posedge clk) immWire2 == $past(immWire1)
  );

  // SWire2 equals SWire1 from the previous clock.
  check_SWire_pipeline: assert property (
    @(posedge clk) SWire2 == $past(SWire1)
  );

  // CinWire2 equals CinWire1 from the previous clock.
  check_CinWire_pipeline: assert property (
    @(posedge clk) CinWire2 == $past(CinWire1)
  );

  // immBit2 equals immBit1 from the previous clock.
  check_immBit_pipeline: assert property (
    @(posedge clk) immBit2 == $past(immBit1)
  );

  // lwSwFlag2 equals lwSwFlag1 from the previous clock.
  check_lwSwFlag_pipeline: assert property (
    @(posedge clk) lwSwFlag2 == $past(lwSwFlag1)
  );

endmodule