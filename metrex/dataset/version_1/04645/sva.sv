// SVA for uart. Bind this to the DUT.
// Focuses on FSM correctness, counters/ticks, data path, flags, and basic protocol timing.

module uart_sva #(
  parameter int CLOCK_DIVIDE      = 217,
  parameter int RX_IDLE           = 0,
  parameter int RX_CHECK_START    = 1,
  parameter int RX_READ_BITS      = 2,
  parameter int RX_CHECK_STOP     = 3,
  parameter int RX_DELAY_RESTART  = 4,
  parameter int RX_ERROR          = 5,
  parameter int RX_RECEIVED       = 6,

  parameter int TX_IDLE           = 0,
  parameter int TX_SENDING        = 1,
  parameter int TX_DELAY_RESTART  = 2
)(
  input  logic        clk,
  input  logic        rst,

  // IO
  input  logic        rx,
  input  logic        tx,
  input  logic        transmit,
  input  logic [7:0]  tx_byte,
  input  logic        received,
  input  logic [7:0]  rx_byte,
  input  logic        is_receiving,
  input  logic        is_transmitting,
  input  logic        recv_error,

  // Internal
  input  logic [10:0] rx_clk_divider,
  input  logic [10:0] tx_clk_divider,

  input  logic  [2:0] recv_state,
  input  logic  [5:0] rx_countdown,
  input  logic  [3:0] rx_bits_remaining,
  input  logic  [7:0] rx_data,

  input  logic        tx_out,
  input  logic  [1:0] tx_state,
  input  logic  [5:0] tx_countdown,
  input  logic  [3:0] tx_bits_remaining,
  input  logic  [7:0] tx_data
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Flag/port consistency
  assert property (received        == (recv_state == RX_RECEIVED));
  assert property (recv_error      == (recv_state == RX_ERROR));
  assert property (is_receiving    == (recv_state != RX_IDLE));
  assert property (is_transmitting == (tx_state  != TX_IDLE));
  assert property (tx == tx_out);
  assert property (rx_byte == rx_data);

  // Clock divider behavior
  assert property ($past(tx_clk_divider) == 11'd1 |-> tx_clk_divider == CLOCK_DIVIDE);
  assert property ($past(tx_clk_divider) != 11'd1 |-> tx_clk_divider == $past(tx_clk_divider) - 11'd1);
  assert property ($past(rx_clk_divider) == 11'd1 |-> rx_clk_divider == CLOCK_DIVIDE);
  assert property ($past(rx_clk_divider) != 11'd1 |-> rx_clk_divider == $past(rx_clk_divider) - 11'd1);

  // TX: idle baseline
  assert property ((tx_state != TX_SENDING) |-> tx_out == 1'b1);

  // TX: start when transmit asserted in IDLE
  assert property ($rose(transmit) && $past(tx_state) == TX_IDLE
                   |-> tx_state == TX_SENDING
                    && tx_out == 1'b0
                    && tx_bits_remaining == 4'd8
                    && tx_countdown == 6'd4
                    && tx_clk_divider == CLOCK_DIVIDE
                    && tx_data == tx_byte);

  // TX: bit edge when countdown hits 0 on a tick
  // Data bit path
  assert property ($past(tx_state) == TX_SENDING
                   && $past(tx_clk_divider) == 11'd1
                   && $past(tx_countdown) == 6'd1
                   && $past(tx_bits_remaining) != 4'd0
                   |-> tx_state == TX_SENDING
                    && tx_countdown == 6'd4
                    && tx_bits_remaining == $past(tx_bits_remaining) - 4'd1
                    && tx_out == $past(tx_data[0])
                    && tx_data == {1'b0, $past(tx_data[7:1])});

  // TX: stop bit and delay restart
  assert property ($past(tx_state) == TX_SENDING
                   && $past(tx_clk_divider) == 11'd1
                   && $past(tx_countdown) == 6'd1
                   && $past(tx_bits_remaining) == 4'd0
                   |-> tx_state == TX_DELAY_RESTART
                    && tx_out == 1'b1
                    && tx_countdown == 6'd8);

  // TX: finish delay and return to IDLE on next tick when countdown hits 0
  assert property ($past(tx_state) == TX_DELAY_RESTART
                   && $past(tx_clk_divider) == 11'd1
                   && $past(tx_countdown) == 6'd1
                   |-> tx_state == TX_IDLE);

  // RX: detect start bit in IDLE
  assert property ($past(recv_state) == RX_IDLE && rx == 1'b0
                   |-> recv_state == RX_CHECK_START
                    && rx_countdown == 6'd2
                    && rx_clk_divider == CLOCK_DIVIDE);

  // RX: check start at sample point
  assert property ($past(recv_state) == RX_CHECK_START
                   && $past(rx_clk_divider) == 11'd1
                   && $past(rx_countdown) == 6'd1
                   && rx == 1'b0
                   |-> recv_state == RX_READ_BITS
                    && rx_bits_remaining == 4'd8
                    && rx_countdown == 6'd4);

  assert property ($past(recv_state) == RX_CHECK_START
                   && $past(rx_clk_divider) == 11'd1
                   && $past(rx_countdown) == 6'd1
                   && rx == 1'b1
                   |-> recv_state == RX_ERROR);

  // RX: read bits at sample points
  // Continue READ_BITS when more remain
  assert property ($past(recv_state) == RX_READ_BITS
                   && $past(rx_clk_divider) == 11'd1
                   && $past(rx_countdown) == 6'd1
                   && $past(rx_bits_remaining) > 4'd1
                   |-> recv_state == RX_READ_BITS
                    && rx_bits_remaining == $past(rx_bits_remaining) - 4'd1
                    && rx_countdown == 6'd4
                    && rx_data == {rx, $past(rx_data[7:1])});

  // Transition to CHECK_STOP on last data bit
  assert property ($past(recv_state) == RX_READ_BITS
                   && $past(rx_clk_divider) == 11'd1
                   && $past(rx_countdown) == 6'd1
                   && $past(rx_bits_remaining) == 4'd1
                   |-> recv_state == RX_CHECK_STOP
                    && rx_bits_remaining == 4'd0
                    && rx_countdown == 6'd4
                    && rx_data == {rx, $past(rx_data[7:1])});

  // RX: check stop at sample point
  assert property ($past(recv_state) == RX_CHECK_STOP
                   && $past(rx_clk_divider) == 11'd1
                   && $past(rx_countdown) == 6'd1
                   && rx == 1'b1
                   |-> recv_state == RX_RECEIVED);

  assert property ($past(recv_state) == RX_CHECK_STOP
                   && $past(rx_clk_divider) == 11'd1
                   && $past(rx_countdown) == 6'd1
                   && rx == 1'b0
                   |-> recv_state == RX_ERROR);

  // RX: post states
  assert property ($past(recv_state) == RX_RECEIVED |-> recv_state == RX_IDLE);
  assert property ($past(recv_state) == RX_ERROR
                   |-> recv_state == RX_DELAY_RESTART && rx_countdown == 6'd8);

  // RX: finish delay and return to IDLE on next tick when countdown hits 0
  assert property ($past(recv_state) == RX_DELAY_RESTART
                   && $past(rx_clk_divider) == 11'd1
                   && $past(rx_countdown) == 6'd1
                   |-> recv_state == RX_IDLE);

  // Optional: countdowns decrement on ticks when not reloaded (TX_SENDING/RX_* paths)
  assert property ($past(tx_clk_divider) == 11'd1
                   && $past(tx_state) == TX_SENDING
                   && $past(tx_countdown) > 6'd1
                   |-> tx_countdown == $past(tx_countdown) - 6'd1);

  assert property ($past(rx_clk_divider) == 11'd1
                   && $past(recv_state) inside {RX_CHECK_START, RX_READ_BITS, RX_CHECK_STOP}
                   && $past(rx_countdown) > 6'd1
                   |-> rx_countdown == $past(rx_countdown) - 6'd1);

  // Coverage: basic TX frame completes
  cover property ($rose(transmit)
                  ##[1:$] ($past(tx_state) == TX_DELAY_RESTART && tx_state == TX_IDLE));

  // Coverage: successful RX frame
  cover property (recv_state == RX_IDLE && rx == 1'b0
                  ##1 recv_state == RX_CHECK_START
                  ##[1:$] recv_state == RX_RECEIVED);

  // Coverage: RX error path
  cover property (recv_state == RX_IDLE && rx == 1'b0
                  ##1 recv_state == RX_CHECK_START
                  ##[1:$] recv_state == RX_ERROR);

endmodule

// Bind into DUT
bind uart uart_sva #(
  .CLOCK_DIVIDE(CLOCK_DIVIDE),
  .RX_IDLE(RX_IDLE),
  .RX_CHECK_START(RX_CHECK_START),
  .RX_READ_BITS(RX_READ_BITS),
  .RX_CHECK_STOP(RX_CHECK_STOP),
  .RX_DELAY_RESTART(RX_DELAY_RESTART),
  .RX_ERROR(RX_ERROR),
  .RX_RECEIVED(RX_RECEIVED),
  .TX_IDLE(TX_IDLE),
  .TX_SENDING(TX_SENDING),
  .TX_DELAY_RESTART(TX_DELAY_RESTART)
) uart_sva_b (
  .clk(clk),
  .rst(rst),
  .rx(rx),
  .tx(tx),
  .transmit(transmit),
  .tx_byte(tx_byte),
  .received(received),
  .rx_byte(rx_byte),
  .is_receiving(is_receiving),
  .is_transmitting(is_transmitting),
  .recv_error(recv_error),

  .rx_clk_divider(rx_clk_divider),
  .tx_clk_divider(tx_clk_divider),

  .recv_state(recv_state),
  .rx_countdown(rx_countdown),
  .rx_bits_remaining(rx_bits_remaining),
  .rx_data(rx_data),

  .tx_out(tx_out),
  .tx_state(tx_state),
  .tx_countdown(tx_countdown),
  .tx_bits_remaining(tx_bits_remaining),
  .tx_data(tx_data)
);