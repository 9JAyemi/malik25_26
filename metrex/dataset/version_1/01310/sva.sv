// SVA for UART_TX
// Bind into DUT (no DUT changes needed)
bind UART_TX UART_TX_sva u_uart_tx_sva();

module UART_TX_sva;
  // Assertions reference DUT internals directly via bind
  default clocking cb @(posedge sys_clk); endclocking
  default disable iff ($initstate)

  localparam logic [3:0] S_IDLE=4'b0000, S_PRE=4'b0010, S_START=4'b0011, S_STOP=4'b0001;

  function automatic bit is_legal(input logic [3:0] s);
    return (s==S_IDLE || s==S_PRE || s==S_START || s==S_STOP || s[3]);
  endfunction

  // State legality
  assert property (is_legal(state));

  // No state change without BaudTick, except allowed IDLE->PRE handshake
  assert property ((!BaudTick && !(state==S_IDLE && RxD_start && RTS)) |=> $stable(state));

  // Handshake and transitions
  assert property ((state==S_IDLE  && RxD_start && RTS) |=> state==S_PRE);
  assert property ((state==S_PRE   && !BaudTick)        |=> state==S_PRE);
  assert property ((state==S_PRE   && BaudTick)         |=> state==S_START);
  assert property ((state==S_START && !BaudTick)        |=> state==S_START);
  assert property ((state==S_START && BaudTick)         |=> state==4'b1000);

  // Data-phase state progression (1000..1111) and STOP entry
  assert property ($past(state[3] && BaudTick)
                   |-> state == (($past(state)==4'b1111) ? S_STOP : $past(state)+1));

  // Stop bit: branch to IDLE or immediate next START on BaudTick
  assert property ((state==S_STOP && BaudTick && !(RxD_start && RTS)) |=> state==S_IDLE);
  assert property ((state==S_STOP && BaudTick &&  (RxD_start && RTS)) |=> state==S_START);

  // Buffer behavior: load, shift, hold
  assert property ($past(RxD_start && (state<4'd2)) |-> RxD_buff == $past(RxD_par));
  assert property ($past(state[3] && BaudTick)      |-> RxD_buff == ($past(RxD_buff) >> 1));
  assert property (!($past(RxD_start && (state<4'd2))) && !($past(state[3] && BaudTick))
                   |-> RxD_buff == $past(RxD_buff));

  // Output mapping: idle/pre/stop high, start low, data equals LSB of buffer
  assert property ((state < 4'd3)   |-> TxD_ser == 1'b1);
  assert property ((state == 4'd3)  |-> TxD_ser == 1'b0);
  assert property ((state[3])       |-> TxD_ser == RxD_buff[0]);

  // Output stable between BaudTicks during data phase
  assert property ($past(state[3] && !BaudTick) |-> TxD_ser == $past(TxD_ser));

  // Serialization correctness at start of data and across shifts
  assert property ($past(state==S_START && BaudTick)
                   |-> (state==4'b1000 && TxD_ser == $past(RxD_buff[0])));
  assert property ($past(state[3] && BaudTick)
                   |-> (state[3] && TxD_ser == $past(RxD_buff[1])));

  // Sanity: TxD_ser never X
  assert property (!$isunknown(TxD_ser));

  // Coverage: start of data, end of data, stop->idle, back-to-back frames
  cover property ($past(state==S_START && BaudTick) && state==4'b1000);
  cover property ($past(state==4'b1111 && BaudTick) && state==S_STOP);
  cover property ($past(state==S_STOP && BaudTick && !(RxD_start && RTS)) && state==S_IDLE);
  cover property ($past(state==S_STOP && BaudTick &&  (RxD_start && RTS)) && state==S_START);
endmodule