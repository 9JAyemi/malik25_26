// SVA checker for ad_xcvr_rx_if
module ad_xcvr_rx_if_sva (
  input                  rx_clk,
  input        [3:0]     rx_ip_sof,
  input        [31:0]    rx_ip_data,
  input                  rx_sof,
  input        [31:0]    rx_data,

  // internal registers from DUT (bound by name)
  input        [31:0]    rx_ip_data_d,
  input        [3:0]     rx_ip_sof_hold,
  input        [3:0]     rx_ip_sof_d
);

  default clocking cb @ (posedge rx_clk); endclocking

  logic past_valid;
  always_ff @ (posedge rx_clk) past_valid <= 1'b1;

  // Basic protocol assumptions/checks
  // Start-of-frame must be one-hot or zero; hold must mirror that invariant
  assert property (cb $onehot0(rx_ip_sof));
  assert property (cb $onehot0(rx_ip_sof_hold));

  // Pipeline register behavior
  assert property (cb past_valid |-> rx_ip_sof_d  == $past(rx_ip_sof));
  assert property (cb past_valid |-> rx_ip_data_d == $past(rx_ip_data));

  // rx_sof is the OR-reduction of previous-cycle rx_ip_sof
  assert property (cb past_valid |-> rx_sof == (|$past(rx_ip_sof)));

  // Hold register update: capture nonzero, otherwise retain
  assert property (cb past_valid && ($past(rx_ip_sof) != 4'h0) |-> rx_ip_sof_hold == $past(rx_ip_sof));
  assert property (cb past_valid && ($past(rx_ip_sof) == 4'h0) |-> rx_ip_sof_hold == $past(rx_ip_sof_hold));

  // Data alignment matches selected hold bit with correct priority
  assert property (cb past_valid |->
    rx_data ==
      (rx_ip_sof_hold[0] ? rx_ip_data
    : rx_ip_sof_hold[1] ? {rx_ip_data[7:0],  $past(rx_ip_data)[31:8]}
    : rx_ip_sof_hold[2] ? {rx_ip_data[15:0], $past(rx_ip_data)[31:16]}
    : rx_ip_sof_hold[3] ? {rx_ip_data[23:0], $past(rx_ip_data)[31:24]}
                        : 32'd0));

  // Minimal functional coverage
  cover property (cb rx_ip_sof == 4'b0001);
  cover property (cb rx_ip_sof == 4'b0010);
  cover property (cb rx_ip_sof == 4'b0100);
  cover property (cb rx_ip_sof == 4'b1000);
  cover property (cb past_valid && (|$past(rx_ip_sof)) && rx_sof);
  cover property (cb rx_ip_sof_hold == 4'b0000 && rx_data == 32'd0);

endmodule

// Bind into the DUT
bind ad_xcvr_rx_if ad_xcvr_rx_if_sva i_ad_xcvr_rx_if_sva (.*);