// SVA for UART_rx
// Bind-friendly checker; references internal regs
module UART_rx_sva #(
  // Mirror DUT params
  parameter int D_BIT  = 8,
  parameter int IDLE   = 0,
  parameter int START  = 1,
  parameter int DATA   = 2,
  parameter int STOP   = 3
)(
  input  logic        clock,
  input  logic        reset,
  input  logic        rx,
  input  logic        s_tick,
  input  logic        rx_done,
  input  logic [7:0]  d_out,
  input  logic [1:0]  current_state,
  input  logic [3:0]  s,
  input  logic [3:0]  n
);

  default clocking cb @(posedge clock); endclocking
  default disable iff (reset);

  // Async reset drives state to IDLE (checked synchronously)
  assert property (@(posedge clock) reset |-> current_state == IDLE);

  // State encoding legal
  assert property (current_state inside {IDLE, START, DATA, STOP});

  // State (and regs) only change on s_tick
  assert property (!s_tick |=> current_state == $past(current_state));
  assert property (!s_tick |-> $stable({s,n,d_out,rx_done}));

  // IDLE behavior
  assert property ((current_state==IDLE && s_tick) |-> (s==0 && rx_done==0));
  assert property ((current_state==IDLE && s_tick && rx==0) |=> current_state==START);
  assert property ((current_state==IDLE && s_tick && rx==1) |=> current_state==IDLE);

  // START: count 0..7 then go DATA; rx_done held low
  assert property ((current_state==START && s_tick && s<7)
                   |=> (current_state==START && s==$past(s)+1));
  assert property ((current_state==START && s_tick) |-> rx_done==0);
  assert property ((current_state==START && s_tick && s>=7)
                   |=> (current_state==DATA && s==0 && n==0));

  // DATA: sub-tick counter increments, bit capture at s==15
  assert property ((current_state==DATA && s_tick && s<15)
                   |=> (current_state==DATA && s==$past(s)+1));
  // Capture/shift exactly at s==15 when n < D_BIT
  assert property ( ($past(current_state)==DATA && $past(s_tick) && $past(s)==15 && $past(n)<D_BIT)
                    |-> (current_state==DATA && s==0
                         && n==$past(n)+1
                         && d_out=={rx, $past(d_out)[7:1]}) );
  // After completing D_BIT captures, go to STOP on next state update
  assert property ( ($past(current_state)==DATA && $past(s_tick) && $past(s)==15 && $past(n)>=D_BIT)
                    |-> (current_state==STOP && s==0) );

  // d_out must not change except on a capture cycle
  assert property ( s_tick && !(current_state==DATA && s==15 && n<D_BIT) |-> $stable(d_out) );

  // n only changes on capture (DATA @ s==15)
  assert property ( s_tick && !(current_state==DATA && s==15) |-> $stable(n) );

  // STOP behavior and rx_done semantics
  // Hold in STOP while s<15 and rx!=0; increment s
  assert property ((current_state==STOP && s_tick && rx!=0 && s<15)
                   |=> (current_state==STOP && s==$past(s)+1));
  // Early restart: rx==0 in STOP -> rx_done=1, next START, clear s/n
  assert property ((current_state==STOP && s_tick && rx==0)
                   |-> (rx_done==1 && s==0 && n==0)
                   |=> current_state==START);
  // Normal stop complete at s>=15 -> rx_done=1, next IDLE
  assert property ((current_state==STOP && s_tick && s>=15)
                   |-> rx_done==1
                   |=> current_state==IDLE);
  // rx_done only asserted in STOP
  assert property (rx_done |-> current_state==STOP);

  // Simple liveness: once DATA started with n==0, eventually reach STOP with n==D_BIT
  assert property ( (current_state==DATA && n==0 && s==0)
                    |-> ##[1:$] (current_state==STOP) );

  // Coverage
  cover property ( (current_state==IDLE && s_tick && rx==0)
                   ##1 (current_state==START)
                   ##[1:$] (current_state==DATA)
                   ##[1:$] (current_state==STOP && rx_done)
                   ##1 (current_state==IDLE) );

  // Cover immediate restart path (STOP -> START via rx==0)
  cover property ( (current_state==STOP && s_tick && rx==0 && rx_done)
                   ##1 (current_state==START) );

endmodule

// Bind example (place in a testbench or bind file):
// bind UART_rx UART_rx_sva #(.D_BIT(8), .IDLE(0), .START(1), .DATA(2), .STOP(3))
//   u_uart_rx_sva(.*);