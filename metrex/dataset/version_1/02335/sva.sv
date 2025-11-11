// SVA for audio_shifter
// Bind into DUT: bind audio_shifter audio_shifter_sva sva();

module audio_shifter_sva;

  // Default clock/reset for most properties
  default clocking cb @(posedge clk); endclocking
  default disable iff (!nreset);

  // ------------------------
  // Basic sanity and mapping
  // ------------------------

  // Asynchronous reset drives shiftcnt to 0 when nreset=0 (checked synchronously)
  assert property (@(posedge clk) !nreset |-> shiftcnt == 9'd0);

  // When out of reset, shiftcnt strictly decrements each cycle
  assert property (nreset && $past(nreset) |-> shiftcnt == $past(shiftcnt) - 9'd1);

  // Output mappings
  assert property (aud_daclrck == shiftcnt[7]);
  assert property (aud_bclk    == ~shiftcnt[2]);
  assert property (aud_xck     == shiftcnt[0]);
  assert property (aud_dacdat  == shift[15]);

  // aud_xck must toggle every active cycle (LSB of a down-counter)
  assert property (nreset && $past(nreset) |-> $changed(aud_xck));

  // No X on clock-like outputs when active
  assert property (!$isunknown({aud_bclk, aud_daclrck, aud_xck}));

  // ------------------------
  // L/R mixer and mux checks
  // ------------------------

  // Registered mux selection matches spec each cycle
  assert property (rdata_mux == (mix ? rdata_mix : {rdata, rdata[13]}));
  assert property (ldata_mux == (mix ? ldata_mix : {ldata, ldata[13]}));

  // ------------------------
  // Shifter behavior
  // ------------------------

  // No update unless shiftcnt[2:0]==0
  assert property ((shiftcnt[2:0] != 3'b000) |=> $stable(shift));

  // Zero insert when shift window active but not at frame start ([6:3] != 0)
  assert property ((shiftcnt[2:0] == 3'b000 && shiftcnt[6:3] != 4'b0000)
                   |=> shift == { $past(shift[14:0]), 1'b0 });

  // Data insert at frame start ([6:3]==0); exchan has no effect on 16-bit result
  assert property ((shiftcnt[2:0] == 3'b000 && shiftcnt[6:3] == 4'b0000)
                   |=> shift == { $past(shift[14:0]), $past(rdata_mux[0]) });

  // ------------------------
  // Coverage
  // ------------------------

  // Counter wrap from 0 -> 0x1FF on next active cycle
  cover property (nreset && shiftcnt==9'd0 ##1 shiftcnt==9'h1FF);

  // Mix paths exercised
  cover property (mix==0 ##1 rdata_mux == {rdata, rdata[13]});
  cover property (mix==0 ##1 ldata_mux == {ldata, ldata[13]});
  cover property (mix==1 ##1 rdata_mux == rdata_mix);
  cover property (mix==1 ##1 ldata_mux == ldata_mix);

  // Shifter: hold, zero-insert, and data-insert paths
  cover property ((shiftcnt[2:0] != 3'b000) ##1 $stable(shift));
  cover property ((shiftcnt[2:0] == 3'b000 && shiftcnt[6:3] != 0));
  cover property ((shiftcnt[2:0] == 3'b000 && shiftcnt[6:3] == 0));

  // Exercise exchan during data-insert edge
  cover property ((shiftcnt[2:0] == 0 && shiftcnt[6:3] == 0 && exchan));

endmodule