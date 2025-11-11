// SVA for module gps
// Focused, concise checks and coverage. Bind into DUT to access internal regs.

module gps_sva;
  // create simple past-valid flags to safely use $past
  bit past_v_clk, past_v_sat;
  initial begin past_v_clk = 0; past_v_sat = 0; end
  always @(posedge clk)      past_v_clk <= 1'b1;
  always @(posedge sat_data) past_v_sat <= 1'b1;

  // Acquisition/reset behavior (asynchronous domain on rst/sat_data)
  // On reset edge, acq regs clear
  assert property (@(posedge rst) ##0 (local_clock==32'd0 && satellite_position==32'd0 && receiver_position==32'd0))
    else $fatal(1, "Acquisition regs not cleared on rst");

  // On sat_data edge (when not in reset), acq regs update as specified
  assert property (@(posedge sat_data) disable iff (!past_v_sat || rst)
                   ##0 (local_clock == $past(local_clock)+32'd1 &&
                        satellite_position == $past(satellite_position)+32'd1 &&
                        receiver_position == $past(receiver_position)+$past(antenna_data)))
    else $fatal(1, "Acquisition update incorrect on sat_data edge");

  // Acq regs only change on sat_data or rst edges (no stray updates)
  assert property ( ($changed(local_clock) || $changed(satellite_position) || $changed(receiver_position))
                    |-> ##0 ($rose(sat_data) || $rose(rst)))
    else $fatal(1, "Acquisition regs changed without sat_data/rst edge");

  // Navigation stage (clk domain)
  // navigation_data matches combinational expression sampled on clk
  assert property (@(posedge clk) (navigation_data == (satellite_position - receiver_position)))
    else $fatal(1, "navigation_data mismatch");

  // Outputs are 1-cycle delayed, zero-extended slices of navigation_data
  assert property (@(posedge clk) disable iff (!past_v_clk)
                   (lat === {20'h0, $past(navigation_data[31:20])} &&
                    lon === {20'h0, $past(navigation_data[19:8])}  &&
                    alt === {24'h0, $past(navigation_data[7:0])}))
    else $fatal(1, "lat/lon/alt not equal to zero-extended slices of prior navigation_data");

  // nav/output regs only change on clk edge (no glitches)
  assert property ( ($changed(navigation_data) || $changed(lat) || $changed(lon) || $changed(alt))
                    |-> ##0 $rose(clk))
    else $fatal(1, "navigation/output regs changed without clk edge");

  // No X/Z on nav/outputs at clk edges
  assert property (@(posedge clk) !$isunknown({navigation_data, lat, lon, alt}))
    else $fatal(1, "X/Z detected on navigation_data/lat/lon/alt at clk edge");

  // Minimal, meaningful coverage
  //  - See both antenna_data=0 and 1 cases at sat_data edge
  cover property (@(posedge sat_data) !rst && (antenna_data==1'b0));
  cover property (@(posedge sat_data) !rst && (antenna_data==1'b1));

  //  - Observe non-zero navigation result and propagated non-zero outputs
  cover property (@(posedge clk) navigation_data != 32'd0);
  cover property (@(posedge clk) (lat != 32'd0 || lon != 32'd0 || alt != 32'd0));

  //  - Reset occurrence
  cover property (@(posedge rst) 1'b1);
endmodule

bind gps gps_sva gps_sva_i;