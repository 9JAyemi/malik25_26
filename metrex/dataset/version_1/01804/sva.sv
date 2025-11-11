// SVA for uart
// Bind this module to the DUT to check key safety, functional timing, and add compact coverage.
module uart_sva #(
  parameter CLOCK_DIVIDE = 1302,
  parameter RX_IDLE = 0, RX_CHECK_START = 1, RX_READ_BITS = 2, RX_CHECK_STOP = 3, RX_DELAY_RESTART = 4, RX_ERROR = 5, RX_RECEIVED = 6,
  parameter TX_IDLE = 0, TX_SENDING = 1, TX_DELAY_RESTART = 2
)(
  input  logic         clk, rst,
  // DUT ports
  input  logic         rx, transmit,
  input  logic [7:0]   tx_byte,
  input  logic         tx, received, is_receiving, is_transmitting, recv_error,
  input  logic [7:0]   rx_byte,
  // DUT internals
  input  logic [10:0]  rx_clk_divider, tx_clk_divider,
  input  logic  [2:0]  recv_state,
  input  logic  [5:0]  rx_countdown,
  input  logic  [3:0]  rx_bits_remaining,
  input  logic  [7:0]  rx_data,
  input  logic         tx_out,
  input  logic  [1:0]  tx_state,
  input  logic  [5:0]  tx_countdown,
  input  logic  [3:0]  tx_bits_remaining,
  input  logic  [7:0]  tx_data
);

default clocking cb @(posedge clk); endclocking
default disable iff (rst);

// Basic encodings and derived outputs
assert property (recv_state inside {RX_IDLE,RX_CHECK_START,RX_READ_BITS,RX_CHECK_STOP,RX_DELAY_RESTART,RX_ERROR,RX_RECEIVED});
assert property (tx_state   inside {TX_IDLE,TX_SENDING,TX_DELAY_RESTART});
assert property (received      == (recv_state == RX_RECEIVED));
assert property (recv_error    == (recv_state == RX_ERROR));
assert property (is_receiving  == (recv_state != RX_IDLE));
assert property (is_transmitting == (tx_state != TX_IDLE));
assert property (tx == tx_out);
assert property (rx_byte == rx_data);

// Reset behavior
assert property (@(posedge clk) rst |-> (recv_state==RX_IDLE && tx_state==TX_IDLE && !is_receiving && !is_transmitting && !received && !recv_error));

// Clock dividers: decrement and reload behavior
// RX divider
assert property ( $past(rx_clk_divider)>11'd1 |-> rx_clk_divider == $past(rx_clk_divider)-11'd1 );
assert property ( $past(rx_clk_divider)==11'd1 |-> rx_clk_divider == CLOCK_DIVIDE && rx_countdown == $past(rx_countdown)-6'd1 );
assert property ( rx_clk_divider != 11'd0 ); // runtime state should never be 0
// TX divider
assert property ( $past(tx_clk_divider)>11'd1 |-> tx_clk_divider == $past(tx_clk_divider)-11'd1 );
assert property ( $past(tx_clk_divider)==11'd1 |-> tx_clk_divider == CLOCK_DIVIDE && tx_countdown == $past(tx_countdown)-6'd1 );
assert property ( tx_clk_divider != 11'd0 );

// RX FSM: start detect
assert property ( $past(recv_state)==RX_IDLE && (rx==1'b0) |->
                  recv_state==RX_CHECK_START && rx_clk_divider==CLOCK_DIVIDE && rx_countdown==6'd2 );

// RX CHECK_START at baud tick
property rx_chkstart_tick;
  $past(recv_state)==RX_CHECK_START && $past(rx_clk_divider)==11'd1 && $past(rx_countdown)==6'd1;
endproperty
assert property ( rx_chkstart_tick && (rx==1'b0) |-> recv_state==RX_READ_BITS && rx_countdown==6'd4 && rx_bits_remaining==4'd8 );
assert property ( rx_chkstart_tick && (rx==1'b1) |-> recv_state==RX_ERROR );

// RX READ_BITS at baud tick: shift LSB-first from rx into MSB of rx_data
assert property (
  $past(recv_state)==RX_READ_BITS && $past(rx_clk_divider)==11'd1 && $past(rx_countdown)==6'd1 |->
    rx_data == { $past(rx), $past(rx_data[7:1]) } &&
    rx_countdown == 6'd4 &&
    rx_bits_remaining == $past(rx_bits_remaining) - 4'd1 &&
    recv_state == ( ($past(rx_bits_remaining)>4'd1) ? RX_READ_BITS : RX_CHECK_STOP )
);

// RX CHECK_STOP at baud tick
assert property (
  $past(recv_state)==RX_CHECK_STOP && $past(rx_clk_divider)==11'd1 && $past(rx_countdown)==6'd1 |->
    recv_state == (rx ? RX_RECEIVED : RX_ERROR)
);

// RX ERROR one-cycle pulse, then delay
assert property ( $past(recv_state)==RX_ERROR |-> recv_state==RX_DELAY_RESTART && rx_countdown==6'd8 );

// RX RECEIVED returns to IDLE next cycle
assert property ( $past(recv_state)==RX_RECEIVED |-> recv_state==RX_IDLE );

// RX stays in DELAY_RESTART until countdown hits zero at tick
assert property (
  $past(recv_state)==RX_DELAY_RESTART && $past(rx_clk_divider)==11'd1 |->
    recv_state == ( ($past(rx_countdown)==6'd1) ? RX_IDLE : RX_DELAY_RESTART )
);

// TX: start of transmission from IDLE
assert property (
  $past(tx_state)==TX_IDLE && transmit |->
    tx_state==TX_SENDING && tx_out==1'b0 && tx_bits_remaining==4'd8 &&
    tx_countdown==6'd4 && tx_clk_divider==CLOCK_DIVIDE && tx_data==tx_byte
);

// TX sending: data bit on each baud tick while bits_remaining>0
assert property (
  $past(tx_state)==TX_SENDING && $past(tx_clk_divider)==11'd1 && $past(tx_countdown)==6'd1 && ($past(tx_bits_remaining)>4'd0) |->
    tx_out == $past(tx_data[0]) &&
    tx_data == {1'b0, $past(tx_data[7:1])} &&
    tx_bits_remaining == $past(tx_bits_remaining)-4'd1 &&
    tx_countdown==6'd4 && tx_state==TX_SENDING
);

// TX after last data bit (bits_remaining==0 at tick): drive stop bit and delay
assert property (
  $past(tx_state)==TX_SENDING && $past(tx_clk_divider)==11'd1 && $past(tx_countdown)==6'd1 && ($past(tx_bits_remaining)==4'd0) |->
    tx_out==1'b1 && tx_countdown==6'd8 && tx_state==TX_DELAY_RESTART
);

// TX stays in DELAY_RESTART until countdown hits zero at tick, then IDLE
assert property (
  $past(tx_state)==TX_DELAY_RESTART && $past(tx_clk_divider)==11'd1 |->
    tx_state == ( ($past(tx_countdown)==6'd1) ? TX_IDLE : TX_DELAY_RESTART )
);

// TX idle line high when not starting
assert property ( tx_state==TX_IDLE && !transmit |-> tx_out==1'b1 );

// Compact coverage
cover property (recv_state==RX_IDLE ##1 (rx==0) ##1 recv_state==RX_CHECK_START ##[1:$] recv_state==RX_READ_BITS ##[1:$] recv_state==RX_CHECK_STOP ##1 recv_state==RX_RECEIVED ##1 recv_state==RX_IDLE);
cover property (recv_state==RX_IDLE ##1 (rx==0) ##1 recv_state==RX_CHECK_START ##[1:$] recv_state==RX_ERROR ##1 recv_state==RX_DELAY_RESTART);
cover property ($rose(transmit) ##1 tx_state==TX_SENDING ##[1:$] tx_state==TX_DELAY_RESTART ##[1:$] tx_state==TX_IDLE);

endmodule

// Bind into DUT (example)
// bind uart uart_sva #(
//   .CLOCK_DIVIDE(CLOCK_DIVIDE),
//   .RX_IDLE(RX_IDLE), .RX_CHECK_START(RX_CHECK_START), .RX_READ_BITS(RX_READ_BITS), .RX_CHECK_STOP(RX_CHECK_STOP), .RX_DELAY_RESTART(RX_DELAY_RESTART), .RX_ERROR(RX_ERROR), .RX_RECEIVED(RX_RECEIVED),
//   .TX_IDLE(TX_IDLE), .TX_SENDING(TX_SENDING), .TX_DELAY_RESTART(TX_DELAY_RESTART)
// ) u_sva (.*);