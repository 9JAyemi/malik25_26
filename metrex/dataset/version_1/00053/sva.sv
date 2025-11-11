// SVA for UART_Tx
// Bind into the DUT to check FSM, counters, timing, data flow, and coverage.

module UART_Tx_sva #(parameter int N=5, parameter int Full=29)
(
  input  logic         Clk,
  input  logic         Reset,
  input  logic  [7:0]  Data,
  input  logic         Send,
  input  logic         Busy,
  input  logic         Tx,
  input  logic         tSend,
  input  logic  [7:0]  Temp,
  input  logic  [N-1:0]Count,
  input  logic  [2:0]  BitCount,
  input  logic  [1:0]  State,
  input  logic         tReset
);

  localparam logic [1:0] Idle=2'b00, Sending=2'b01, StopBit=2'b11, Done=2'b10;

  default clocking cb @(posedge Clk); endclocking

  // tReset is the synchronous reset used by DUT. Use it as disable.
  // Also relate it to Reset and check reset values.
  assert property (@(posedge Clk) tReset |-> $past(Reset));

  // Reset state (next-cycle effect of tReset)
  assert property (@(posedge Clk) tReset |-> Busy==0 && Tx==1 && State==Idle && Count==0 && BitCount==0 && tSend==0);

  // tSend is a 1-cycle registered version of Send
  assert property (@(posedge Clk) disable iff (tReset) tSend == $past(Send));

  // Idle invariants
  assert property (@(posedge Clk) disable iff (tReset) (State==Idle) |-> (Busy==0 && Tx==1));
  assert property (@(posedge Clk) disable iff (tReset) (State!=Idle) |-> Busy);

  // When Count>0, only Count decrements; all other key regs hold
  assert property (@(posedge Clk) disable iff (tReset)
                   (|Count) |=> (Count == $past(Count)-1) && $stable(State) && $stable(Tx) && $stable(BitCount) && $stable(Busy));

  // Accept start: on Idle with Count==0 and tSend, next cycle go Sending with start-bit 0, reloads and inits
  assert property (@(posedge Clk) disable iff (tReset)
                   (State==Idle && (Count==0) && tSend)
                   |=> (State==Sending && Busy && Tx==0 && Count==Full && BitCount==3'd7 && Temp==$past(Data)));

  // Idle with no send: remain idle, Tx high, Busy low, Count stays 0
  assert property (@(posedge Clk) disable iff (tReset)
                   (State==Idle && (Count==0) && !tSend)
                   |=> (State==Idle && Busy==0 && Tx==1 && Count==0));

  // Sending: reload each bit period
  assert property (@(posedge Clk) disable iff (tReset)
                   (State==Sending && (Count==0)) |=> (Count==Full));

  // Sending: shift/Tx behavior at bit boundary; BitCount decrements when not last bit
  assert property (@(posedge Clk) disable iff (tReset)
                   (State==Sending && (Count==0) && (BitCount!=0))
                   |=> (State==Sending && BitCount == $past(BitCount)-1 && Tx == $past(Temp[0])));
  // Last data bit -> StopBit next, Tx takes prior LSB value
  assert property (@(posedge Clk) disable iff (tReset)
                   (State==Sending && (Count==0) && (BitCount==0))
                   |=> (State==StopBit && Tx == $past(Temp[0])));

  // StopBit: reload and drive stop bit high
  assert property (@(posedge Clk) disable iff (tReset)
                   (State==StopBit && (Count==0)) |=> (State==Done && Count==Full && Tx==1));

  // Done: hold busy if tSend, otherwise drop to Idle and deassert Busy
  assert property (@(posedge Clk) disable iff (tReset)
                   (State==Done && (Count==0) && tSend) |=> (State==Done && Busy));
  assert property (@(posedge Clk) disable iff (tReset)
                   (State==Done && (Count==0) && !tSend) |=> (State==Idle && !Busy));

  // No mid-bit glitch: Tx stable while Count!=0
  assert property (@(posedge Clk) disable iff (tReset) (|Count) |-> $stable(Tx));

  // Coverage: complete frame traversal
  cover property (@(posedge Clk) disable iff (tReset)
                  (State==Idle && (Count==0) && tSend)
                  |=> State==Sending ##[1:$] State==StopBit ##1 State==Done ##1 State==Idle);

  // Coverage: 8 data-bit emission (BitCount reaches 0 in Sending at a boundary)
  cover property (@(posedge Clk) disable iff (tReset)
                  (State==Sending && (Count==0) && (BitCount==0)));

endmodule

bind UART_Tx UART_Tx_sva #(.N(N), .Full(Full)) uart_tx_sva_i
(
  .Clk(Clk),
  .Reset(Reset),
  .Data(Data),
  .Send(Send),
  .Busy(Busy),
  .Tx(Tx),
  .tSend(tSend),
  .Temp(Temp),
  .Count(Count),
  .BitCount(BitCount),
  .State(State),
  .tReset(tReset)
);