// SVA checker for comparator. Bind this to the DUT.
// Focuses on protocol, strobes, counters, bitslip, and error-hold behavior.

module comparator_sva #(
  parameter int WIDTH        = 8,
  parameter int ERROR_COUNT  = 8,
  parameter int ERROR_HOLD   = 2500000
)(
  input  logic                 CLK,
  input  logic                 RST,
  input  logic                 TX_STB,
  input  logic [WIDTH-1:0]     TX_DAT,
  input  logic                 RX_STB,
  input  logic [WIDTH-1:0]     RX_DAT,
  input  logic                 RX_BITSLIP,
  input  logic                 O_ERROR
);

  default clocking cb @(posedge CLK); endclocking
  default disable iff (RST);

  // Sanity: i_rdy is a degenerate AND of rx_valid with itself
  assert property (i_rdy == rx_valid);

  // tx_valid protocol and data capture/hold
  assert property ((!tx_valid && TX_STB && !i_rdy) |=> tx_valid);
  assert property (i_rdy |=> !tx_valid);
  assert property ((tx_valid && !i_rdy) |=> tx_valid && $stable(tx_dat));
  assert property ((!tx_valid && TX_STB && !i_rdy) |=> tx_dat == $past(TX_DAT));

  // rx_valid protocol and data capture/hold
  assert property ((!rx_valid && RX_STB) |=> rx_valid);
  assert property (i_rdy |=> !rx_valid);
  assert property ((rx_valid && !i_rdy) |=> rx_valid && $stable(rx_dat));
  assert property ((!rx_valid && RX_STB) |=> rx_dat == $past(RX_DAT));

  // Compare strobe and result timing
  assert property (i_rdy |=> x_stb ##1 !x_stb);           // one-cycle pulse after i_rdy
  assert property (x_stb |-> $past(i_rdy) && !x_stb);     // pulse originates from prior i_rdy
  assert property (i_rdy |=> x_error == $past(rx_dat != tx_dat));
  assert property (!i_rdy |=> $stable(x_error));

  // Error counter: increments on error events, resets after bitslip pulse
  assert property ((x_stb && x_error) |=> count_err == $past(count_err) + 1);
  assert property ($rose(o_bitslip) |=> count_err == 0);

  // Bitslip: single-cycle pulse at/after threshold; output tie-off
  assert property ($rose(o_bitslip) |-> $past(count_err) >= ERROR_COUNT);
  assert property (o_bitslip |=> !o_bitslip);
  assert property (RX_BITSLIP == o_bitslip);

  // Error hold timer/output relationships
  assert property (O_ERROR == !o_cnt[32]);                 // direct functional tie-off
  assert property ((x_stb && x_error) |=> O_ERROR);        // reload drives O_ERROR high
  assert property ((o_cnt[32] && !(x_stb && x_error)) |=> o_cnt[32]); // saturates when expired
  assert property ((!o_cnt[32] && !(x_stb && x_error)) |=> o_cnt <= $past(o_cnt)); // non-increasing while counting

  // Coverage
  cover property (i_rdy);                                  // handshake observed
  cover property (x_stb && !x_error);                      // good compare
  cover property (x_stb && x_error);                       // bad compare
  cover property ((x_stb && x_error)[*ERROR_COUNT] ##1 $rose(o_bitslip)); // threshold reached -> bitslip
  cover property ((x_stb && x_error) ##[1:ERROR_HOLD+2] !O_ERROR);        // error hold eventually expires

endmodule

// Bind into all comparator instances
bind comparator comparator_sva #(
  .WIDTH(WIDTH),
  .ERROR_COUNT(ERROR_COUNT),
  .ERROR_HOLD(ERROR_HOLD)
) comparator_sva_i (
  .CLK(CLK),
  .RST(RST),
  .TX_STB(TX_STB),
  .TX_DAT(TX_DAT),
  .RX_STB(RX_STB),
  .RX_DAT(RX_DAT),
  .RX_BITSLIP(RX_BITSLIP),
  .O_ERROR(O_ERROR)
);