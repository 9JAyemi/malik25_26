// SVA bind module for stratixii_lvds_rx_deser
module stratixii_lvds_rx_deser_sva #(parameter int W = 1) (
  input logic                 clk,
  input logic                 datain,
  input logic                 devclrn,
  input logic                 devpor,
  input logic [W-1:0]         dataout
);
  // Derived synchronous reset
  logic rst; assign rst = devclrn || devpor;

  // Guard first-cycle $past
  logic past_valid;
  initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;

  // Sanity on width (design requires W>=2 due to slice [W-2:0])
  initial assert (W >= 2)
    else $fatal(1, "stratixii_lvds_rx_deser: channel_width (W) must be >= 2");

  default clocking cb @(posedge clk); endclocking

  // Reset drives zeros
  a_reset_zero: assert property (cb (rst && past_valid) |-> dataout == '0);

  // Core shift behavior: next dataout equals shifted prior dataout plus prior datain
  a_shift_vec: assert property (cb disable iff (rst || !past_valid)
                                dataout == {$past(dataout[W-2:0]), $past(datain)});

  // No X/Z on key signals when out of reset
  a_no_x_out:  assert property (cb disable iff (rst || !past_valid) !$isunknown(dataout));
  a_no_x_in:   assert property (cb disable iff (rst || !past_valid) !$isunknown(datain));

  // Coverage
  c_reset_seen:      cover property (cb rst);
  c_reset_release:   cover property (cb past_valid && $fell(rst));
  c_shift_activity:  cover property (cb disable iff (rst || !past_valid) $changed(dataout));
  // Fill ones: after W consecutive 1s on datain, output becomes all ones
  c_fill_ones:       cover property (cb disable iff (rst)
                                     (datain==1'b1)[*W] and (dataout == {W{1'b1}}));
  // Propagation to MSB after W cycles
  c_msb_latency_1:   cover property (cb disable iff (rst || !past_valid)
                                     datain ##W dataout[W-1]);
  c_msb_latency_0:   cover property (cb disable iff (rst || !past_valid)
                                     !datain ##W !dataout[W-1]);
endmodule

// Bind the SVA to the DUT
bind stratixii_lvds_rx_deser
  stratixii_lvds_rx_deser_sva #(.W($bits(dataout)))
  stratixii_lvds_rx_deser_sva_i (
    .clk     (clk),
    .datain  (datain),
    .devclrn (devclrn),
    .devpor  (devpor),
    .dataout (dataout)
  );