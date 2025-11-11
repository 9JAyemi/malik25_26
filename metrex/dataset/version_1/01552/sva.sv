// SVA for uart. Bind into the DUT to check key protocol, state transitions, data shifting, and flags.
// Focused, concise, and high-signal-coverage.

bind uart uart_sva u_uart_sva();

module uart_sva;

  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Reset behavior
  assert property (@(posedge clk) rst |-> (recv_state == RX_IDLE && tx_state == TX_IDLE));

  // Sanity: legal state encodings
  assert property (recv_state inside {RX_IDLE, RX_CHECK_START, RX_READ_BITS, RX_CHECK_STOP, RX_DELAY_RESTART, RX_ERROR, RX_RECEIVED});
  assert property (tx_state   inside {TX_IDLE, TX_SENDING, TX_DELAY_RESTART});

  // Output flags vs. state
  assert property (is_receiving == (recv_state != RX_IDLE));
  assert property (is_transmitting == (tx_state != TX_IDLE));
  assert property (received == (recv_state == RX_RECEIVED));
  assert property (recv_error == (recv_state == RX_ERROR));
  assert property (!(received && recv_error));

  // received/recv_error are single-cycle pulses
  assert property (received   |=> !received);
  assert property (recv_error |=> !recv_error);

  // Basic signal X-checks
  assert property (!$isunknown({rx, tx, received, recv_error, is_receiving, is_transmitting}));

  // RX FSM: start detect from idle
  assert property ((recv_state == RX_IDLE && !rx) |=> (recv_state == RX_CHECK_START && rx_countdown == 2));

  // RX FSM: validate start or error at CHECK_START
  assert property ((recv_state == RX_CHECK_START && rx_countdown == 0 && !rx)
                   |=> (recv_state == RX_READ_BITS && rx_bits_remaining == 8 && rx_countdown == 4));
  assert property ((recv_state == RX_CHECK_START && rx_countdown == 0 &&  rx)
                   |=> (recv_state == RX_ERROR));

  // RX FSM: bit reads and shifting
  assert property ((recv_state == RX_READ_BITS && rx_countdown == 0 && rx_bits_remaining > 1)
                   |=> (recv_state == RX_READ_BITS &&
                        rx_bits_remaining == $past(rx_bits_remaining) - 1 &&
                        rx_data == {rx, $past(rx_data[7:1])} &&
                        rx_countdown == 4));

  // RX FSM: final bit to STOP check
  assert property ((recv_state == RX_READ_BITS && rx_countdown == 0 && rx_bits_remaining == 1)
                   |=> (recv_state == RX_CHECK_STOP &&
                        rx_data == {rx, $past(rx_data[7:1])} &&
                        rx_countdown == 4));

  // RX FSM: stop-bit check -> received or error
  assert property ((recv_state == RX_CHECK_STOP && rx_countdown == 0 && rx)
                   |=> (recv_state == RX_RECEIVED));
  assert property ((recv_state == RX_CHECK_STOP && rx_countdown == 0 && !rx)
                   |=> (recv_state == RX_ERROR));

  // RX FSM: terminal states sequencing
  assert property ((recv_state == RX_RECEIVED) |=> (recv_state == RX_IDLE));
  assert property ((recv_state == RX_ERROR)    |=> (recv_state == RX_DELAY_RESTART && rx_countdown == 8));
  assert property ((recv_state == RX_DELAY_RESTART && rx_countdown > 0) |=> (recv_state == RX_DELAY_RESTART));
  assert property ((recv_state == RX_DELAY_RESTART && rx_countdown == 0) |=> (recv_state == RX_IDLE));

  // TX FSM: kick-off from idle on transmit
  assert property ((tx_state == TX_IDLE && transmit)
                   |=> (tx_state == TX_SENDING &&
                        tx_out == 1'b0 &&
                        tx_bits_remaining == 8 &&
                        tx_countdown == 4 &&
                        tx_data == $past(tx_byte)));

  // TX FSM: sending bits (shift and output LSB)
  assert property ((tx_state == TX_SENDING && tx_countdown == 0 && tx_bits_remaining > 0)
                   |=> (tx_state == TX_SENDING &&
                        tx_bits_remaining == $past(tx_bits_remaining) - 1 &&
                        tx_out == $past(tx_data[0]) &&
                        tx_data == {1'b0, $past(tx_data[7:1])} &&
                        tx_countdown == 4));

  // TX FSM: after last bit -> stop bit and delay
  assert property ((tx_state == TX_SENDING && tx_countdown == 0 && tx_bits_remaining == 0)
                   |=> (tx_state == TX_DELAY_RESTART &&
                        tx_out == 1'b1 &&
                        tx_countdown == 8));

  // TX FSM: hold stop during delay, then return to idle
  assert property ((tx_state == TX_DELAY_RESTART && tx_countdown > 0)
                   |=> (tx_state == TX_DELAY_RESTART && tx_out == 1'b1));
  assert property ((tx_state == TX_DELAY_RESTART && tx_countdown == 0)
                   |=> (tx_state == TX_IDLE));

  // TX: ignore transmit while busy (does not change state immediately)
  assert property ((tx_state != TX_IDLE && transmit) |-> $stable(tx_state));

  // Coverage: one successful TX frame
  cover property ((tx_state == TX_IDLE && transmit)
                  ##1 (tx_state == TX_SENDING)
                  ##[1:$] (tx_state == TX_DELAY_RESTART)
                  ##[1:$] (tx_state == TX_IDLE));

  // Coverage: one successful RX frame
  cover property ((recv_state == RX_IDLE && !rx)
                  ##1 (recv_state == RX_CHECK_START)
                  ##[1:$] (recv_state == RX_READ_BITS)
                  ##[1:$] (recv_state == RX_CHECK_STOP)
                  ##1 (recv_state == RX_RECEIVED));

  // Coverage: one RX error path
  cover property ((recv_state == RX_CHECK_STOP && rx_countdown == 0 && !rx)
                  ##1 (recv_state == RX_ERROR));

endmodule