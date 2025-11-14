// SVA for ad_csc_1
// Bind inside DUT scope so we can check internal regs concisely.
module ad_csc_1_sva #(parameter DELAY_DATA_WIDTH = 16, parameter DW = DELAY_DATA_WIDTH-1) ();

  default clocking cb @(posedge clk); endclocking

  // 1) Pipeline capture checks
  assert property (delayed_data == $past(data));
  assert property (delayed_sync == $past(sync[0]));

  // 2) Sync path mapping and vector-scalar intent
  assert property (CrYCb_sync == delayed_sync);
  assert property (csc_sync_1[0] == CrYCb_sync);
  if (DW > 0) begin
    assert property (csc_sync_1[DW:1] == '0); // higher bits forced 0
    // Optional: flag if unused upper sync bits are ever set (width-mismatch awareness)
    assert property (sync[DW:1] == '0);
  end

  // 3) Color calculation and truncation
  assert property (CrYCb_calc ==
                   (C1 * delayed_data[23:16]) +
                   (C2 * delayed_data[15:8])  +
                   (C3 * delayed_data[7:0])   + C4);

  assert property (CrYCb_calc_trunc == CrYCb_calc[23:8]);

  // Output data slice equivalence
  assert property (csc_data_1 == CrYCb_calc_trunc[7:0]);
  assert property (csc_data_1 == CrYCb_calc[15:8]);

  // 4) CrYCb_data behavior
  // Clear on sync pulse
  assert property (delayed_sync |=> (CrYCb_data == 24'h0) && CrYCb_sync);
  // Shift/accumulate when not in sync (note zero-extend to 24b per RTL width mismatch)
  assert property (!delayed_sync |=> (CrYCb_data == {8'h00, $past(CrYCb_data[7:0]), $past(csc_data_1)}) && !CrYCb_sync);

  // 5) Basic X/Z hygiene on key control/outputs
  assert property (!$isunknown({delayed_sync, CrYCb_sync, csc_sync_1[0]}));
  assert property (!$isunknown(csc_data_1));

  // Coverage
  cover property (delayed_sync);                   // hit sync branch
  cover property (!delayed_sync);                  // hit non-sync branch
  cover property (!delayed_sync ##1 !delayed_sync);// two consecutive shifts
  cover property (csc_data_1 == 8'h00);
  cover property (csc_data_1 == 8'hFF);

endmodule

bind ad_csc_1 ad_csc_1_sva #(.DELAY_DATA_WIDTH(DELAY_DATA_WIDTH), .DW(DELAY_DATA_WIDTH-1)) i_ad_csc_1_sva();