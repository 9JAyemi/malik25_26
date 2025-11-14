// SVA for Zigbee — concise, high-value checks and coverage.
// Bind this after compiling the DUT.

module Zigbee_sva #(
  parameter [3:0] RX_CHANNEL = 4'b0000
)(
  input  logic [7:0] data_in,
  input  logic [3:0] channel,
  input  logic       TX_EN,
  input  logic       RX_EN,
  input  logic [7:0] RX_IN,
  input  logic [7:0] data_out,
  input  logic       TX_OUT
);

  // TX: TX_OUT must reflect data_in at TX_EN edge
  property p_tx_out_follows_data_in;
    @(posedge TX_EN) 1 |=> ##0 (TX_OUT == $past(data_in, 1, posedge TX_EN));
  endproperty
  assert property (p_tx_out_follows_data_in);

  // TX: known values at/after TX_EN edge
  assert property (@(posedge TX_EN) !$isunknown({TX_EN, data_in}) |=> ##0 !$isunknown(TX_OUT));

  // TX_OUT should not change on RX_EN edges unless TX_EN also rises
  assert property (@(posedge RX_EN) !$rose(TX_EN) |=> ##0 $stable(TX_OUT));

  // RX: on channel match, data_out must reflect RX_IN at RX_EN edge
  property p_rx_updates_on_match;
    @(posedge RX_EN) (channel == RX_CHANNEL) |=> ##0 (data_out == $past(RX_IN, 1, posedge RX_EN));
  endproperty
  assert property (p_rx_updates_on_match);

  // RX: on channel mismatch, data_out must hold
  property p_rx_holds_on_mismatch;
    @(posedge RX_EN) (channel != RX_CHANNEL) |=> ##0 $stable(data_out);
  endproperty
  assert property (p_rx_holds_on_mismatch);

  // RX: known values when sampled; known data_out after update
  assert property (@(posedge RX_EN) !$isunknown({RX_EN, RX_IN, channel}));
  assert property (@(posedge RX_EN) (channel == RX_CHANNEL) |=> ##0 !$isunknown(data_out));

  // data_out should not change on TX_EN edges unless RX_EN also rises
  assert property (@(posedge TX_EN) !$rose(RX_EN) |=> ##0 $stable(data_out));

  // Functional coverage
  cover property (@(posedge TX_EN) 1);
  cover property (@(posedge RX_EN) (channel == RX_CHANNEL));
  cover property (@(posedge RX_EN) (channel != RX_CHANNEL));
  cover property (@(posedge RX_EN) (channel == RX_CHANNEL) ##0 (data_out == $past(RX_IN, 1, posedge RX_EN)));
  cover property (@(posedge RX_EN) $rose(TX_EN)); // simultaneous TX/RX enable

endmodule

// Bind into DUT; picks up DUT's RX_CHANNEL value.
bind Zigbee Zigbee_sva #(.RX_CHANNEL(RX_CHANNEL)) u_zigbee_sva (
  .data_in   (data_in),
  .channel   (channel),
  .TX_EN     (TX_EN),
  .RX_EN     (RX_EN),
  .RX_IN     (RX_IN),
  .data_out  (data_out),
  .TX_OUT    (TX_OUT)
);