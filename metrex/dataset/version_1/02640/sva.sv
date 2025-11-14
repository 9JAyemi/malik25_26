// SystemVerilog Assertions for i2s_tx
// Bind these SVA to the DUT; concise but checks key intent and provides basic coverage.

module i2s_tx_sva;

  // Pull parameter values and local aliases
  localparam int DW = DATA_WIDTH;
  localparam int LR = LR_BIT;
  localparam int SK = SCK_BIT;
  localparam int MK = MCK_BIT;

  bit past_valid;
  initial past_valid = 0;
  always @(posedge clk) past_valid <= 1;

  default clocking cb @(posedge clk); endclocking
  default disable iff (!past_valid);

  // No-X on observable outputs
  assert property (!$isunknown({mck, sck, lrclk, sdata}));

  // Counter increments and output-decode correctness
  assert property (mck_div == $past(mck_div) + 1);
  assert property (mck   == mck_div[MK]);
  assert property (lrclk == mck_div[LR]);
  assert property (sck   == mck_div[SK]);
  assert property (mck == !$past(mck)); // LSB must toggle every cycle

  // Previous-sample mirrors and edge-detectors
  assert property (sck_prev    == $past(sck));
  assert property (lrclk_prev  == $past(lrclk));
  assert property (sck_neg     == ($past(sck) && !sck));
  assert property (lrclk_change== (lrclk != $past(lrclk)));

  // Alignment: LR bit toggle implies SCK bit falls in same increment
  assert property ((mck_div[LR] != $past(mck_div[LR]))
                   |-> ($past(mck_div[SK]) && !mck_div[SK]));

  // Data path: load/shift and output timing
  assert property ((sck_neg && !lrclk_change) |=> ch_data == ($past(ch_data) << 1));
  assert property ((sck_neg &&  lrclk_change) |=> ch_data == $past(sgnd_data));
  assert property ( sck_neg                   |=> sdata   == $past(ch_data[DW-1]));
  assert property (!sck_neg                   |=> sdata   == $past(sdata));

  // Fake-data stepping only on channel load
  assert property ((sck_neg &&  lrclk_change) |=> fake_data == $past(fake_data) + 32'd178956972);
  assert property ((sck_neg && !lrclk_change) |=> fake_data == $past(fake_data));

  // Parameter/index sanity
  initial begin
    assume (DW >= 1);
    assert (LR < $bits(mck_div));
    assert (SK >= 0 && SK < $bits(mck_div));
    assert (MK >= 0 && MK < $bits(mck_div));
  end

  // Minimal functional coverage
  cover property (sck_neg);
  cover property (lrclk_change);
  cover property (lrclk_change ##1 (!lrclk_change && sck_neg)[*DW] ##1 lrclk_change);
  cover property ($rose(sdata) and $fell(sdata));

endmodule

bind i2s_tx i2s_tx_sva;