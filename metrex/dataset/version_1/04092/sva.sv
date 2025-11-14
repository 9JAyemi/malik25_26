// SVA for uart_transmitter
// Bind this module to the DUT: bind uart_transmitter uart_transmitter_sva #(.CLK(CLK), .BAUD(BAUD)) uart_tx_chk (.*);

module uart_transmitter_sva
  #(parameter int unsigned CLK=50_000_000,
    parameter int unsigned BAUD=9600)
(
  input  logic        clk,
  input  logic        rst,
  input  logic [7:0]  data,
  input  logic        nextch,
  input  logic        txd,

  // internal DUT signals (connected by bind with .*)
  input  logic        state,
  input  logic        next,
  input  logic [31:0] cnt,
  input  logic [4:0]  bitcnt,
  input  logic [9:0]  rshift,
  input  logic        shift, load, clear, getch, gotch
);

  localparam int unsigned RATE = CLK/BAUD;
  localparam bit INIT = 1'b0;
  localparam bit TXD  = 1'b1;

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst);

  // Helpers
  wire tick = (cnt >= RATE);

  // Baud tick spacing exactly RATE cycles
  assert property ( tick |-> (!tick)[*RATE-1] ##1 tick );

  // State/shift/rshift/bitcnt only update on tick
  assert property ( !tick |-> $stable({state, bitcnt, rshift}) );

  // Combinational control correctness by state
  assert property ( state==INIT |-> (load && !shift && !clear && !getch && txd==1 && next==TXD) );
  assert property ( state==TXD && bitcnt<9 |-> (shift && !clear && !load && txd==rshift[0] && next==TXD) );
  assert property ( state==TXD && bitcnt>=9 |-> (!shift && clear && getch && next==INIT && txd==1) );

  // State follows next on tick
  assert property ( tick |-> state == $past(next) );

  // Load/shift/clear effects on tick
  assert property ( tick && load  |-> rshift == {1'b1, $past(data), 1'b0} );
  assert property ( tick && shift |-> rshift == ($past(rshift) >> 1) && bitcnt == $past(bitcnt)+1 );
  assert property ( tick && clear |-> bitcnt == 0 && gotch == 0 );

  // Bit counter bounds
  assert property ( bitcnt <= 9 );

  // TXD stable between ticks
  assert property ( !tick |-> txd == $past(txd) );

  // Handshake: nextch is a single-cycle pulse, causes gotch, and only when requested
  assert property ( $rose(nextch) |-> $past(getch && !gotch) );
  assert property ( $rose(nextch) |=> (!nextch && gotch) );
  // Request emitted exactly one cycle after end-of-frame tick if not already got
  assert property ( tick && state==TXD && bitcnt>=9 && !$past(gotch) |=> $rose(nextch) );
  // No request if already got
  assert property ( tick && state==TXD && bitcnt>=9 &&  $past(gotch) |=> !$rose(nextch) );

  // UART framing: start(0), 8 data LSB-first, stop(1)
  property p_uart_frame;
    var logic [7:0] d;
    (tick && state==INIT && load, d = data)
    |=> (txd==1'b0)                                      // start
        ##1 tick ##0 (txd==d[0])
        ##1 tick ##0 (txd==d[1])
        ##1 tick ##0 (txd==d[2])
        ##1 tick ##0 (txd==d[3])
        ##1 tick ##0 (txd==d[4])
        ##1 tick ##0 (txd==d[5])
        ##1 tick ##0 (txd==d[6])
        ##1 tick ##0 (txd==d[7])
        ##1 tick ##0 (txd==1'b1);                        // stop
  endproperty
  assert property (p_uart_frame);

  // Coverage
  cover property (p_uart_frame);
  cover property ( $rose(nextch) );
  cover property ( tick && state==TXD && bitcnt==9 ); // end-of-frame tick

endmodule