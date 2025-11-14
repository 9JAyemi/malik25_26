// SVA for uart_transmitter
// Focus: correctness of baud ticking, shift/load precedence, serial framing, stability, and coverage.
// Bind into DUT to observe internals.

module uart_transmitter_sva
(
  input logic                     clk,
  input logic                     uart_tx,
  input logic                     rx_new_byte,
  input logic [7:0]               rx_byte,
  input logic                     tx_ready,

  input logic [15:0]              delay_cnt,
  input logic [9:0]               state,
  input logic [9:0]               outgoing,
  input logic [15:0]              baud_delay
);

  default clocking cb @(posedge clk); endclocking

  // Basic invariants
  // Static sanity (avoid degenerate baud = 0)
  initial assert (baud_delay >= 16'd1);

  // Combinational mappings
  assert property (uart_tx == outgoing[0]);
  assert property (tx_ready == (state[0] & ~rx_new_byte));

  // Abbreviation
  wire tick = (delay_cnt >= baud_delay);
  wire load = (rx_new_byte && state[0]);

  // delay_cnt behavior
  assert property ( (tick || load) |=> delay_cnt == 16'd0 );
  assert property ( !(tick || load) |=> delay_cnt == $past(delay_cnt) + 16'd1 );
  assert property ( delay_cnt <= baud_delay );

  // Shift vs load behavior and precedence
  // Pure shift on tick when no load
  assert property ( tick && !load |=> state   == {1'b1, $past(state  [9:1])} );
  assert property ( tick && !load |=> outgoing== {1'b1, $past(outgoing[9:1])} );

  // Load when allowed (also when tick and load coincide, load wins)
  assert property ( load |=> state    == 10'd0 );
  assert property ( load |=> outgoing == {1'b1, $past(rx_byte), 1'b0} );
  assert property ( tick && load |=> state    == 10'd0 );
  assert property ( tick && load |=> outgoing == {1'b1, $past(rx_byte), 1'b0} );

  // State/outgoing and tx may only change on tick or load
  assert property ( $changed(state)    |-> $past(tick || load) );
  assert property ( $changed(outgoing) |-> $past(tick || load) );
  assert property ( $changed(uart_tx)  |-> $past(tick || load) );

  // tx idle level when ready
  assert property ( tx_ready |-> uart_tx == 1'b1 );

  // Exact serial framing and data sequence (LSB-first), checked at tick boundaries
  // Start bit immediately after load; then after each tick the next bit appears next cycle.
  property p_frame_bits;
    bit [7:0] b;
    (load, b = rx_byte)
      |=>  uart_tx == 1'b0
      ##[1:$] tick ##1 (uart_tx == b[0])
      ##[1:$] tick ##1 (uart_tx == b[1])
      ##[1:$] tick ##1 (uart_tx == b[2])
      ##[1:$] tick ##1 (uart_tx == b[3])
      ##[1:$] tick ##1 (uart_tx == b[4])
      ##[1:$] tick ##1 (uart_tx == b[5])
      ##[1:$] tick ##1 (uart_tx == b[6])
      ##[1:$] tick ##1 (uart_tx == b[7])
      ##[1:$] tick ##1 (uart_tx == 1'b1);
  endproperty
  assert property (p_frame_bits);

  // Return-to-idle timing: state[0] becomes 1 exactly after 10 ticks from load
  // (stays 0 for 9 ticks, goes 1 after 10th tick)
  property p_return_idle;
    (load)
      |->  (##[1:$] tick)[*9] ##[1:$] tick ##1 state[0] == 1'b1;
  endproperty
  assert property (p_return_idle);

  // Stability between events: no outputs glitch without tick/load
  assert property ( !(tick || load) |=> $stable(state)    );
  assert property ( !(tick || load) |=> $stable(outgoing) );
  assert property ( !(tick || load) |=> $stable(uart_tx)  );

  // Coverage
  cover property ( load );                                       // accept a byte
  cover property ( load ##[1:$] tick ##1 uart_tx == 1'b0 );      // start bit driven
  cover property ( load ##[1:$] tick ##1 uart_tx == 1'b1 );      // stop bit eventually driven
  cover property ( tick && load );                               // coincident tick+load case
  cover property ( load ##[1:$] ( (##[1:$] tick)[*10] ) ##1 load ); // back-to-back frames asap
  cover property ( (load, rx_byte==8'h00) );
  cover property ( (load, rx_byte==8'hFF) );

endmodule

// Bind into DUT
bind uart_transmitter uart_transmitter_sva
  u_uart_transmitter_sva (
    .clk,
    .uart_tx,
    .rx_new_byte,
    .rx_byte,
    .tx_ready,
    .delay_cnt,
    .state,
    .outgoing,
    .baud_delay
  );