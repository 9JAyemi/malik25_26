// SVA for UART_TX
// Bind into the DUT to access internal signals/state
module UART_TX_sva;
  // This module is intended to be bound inside UART_TX scope
  // so internal names (state, data_reg, data_counter, ...) are visible.

  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Mirror localparams for state compare
  localparam int START = (1 << 0);
  localparam int DATA  = (1 << 1);
  localparam int END   = (1 << 2);

  // Reset values applied next cycle after rst high
  assert property (rst |=> (state == END && tx == 1 && data_accepted == 0));

  // No-baud-edge behavior: state/tx/counters/data_reg hold; data_accepted deasserts
  assert property (!baud_edge |-> ($stable(state) && $stable(tx) &&
                                   $stable(data_counter) && $stable(data_reg) &&
                                   !data_accepted));

  // Legalize/recover from illegal state on a baud tick
  assert property (baud_edge && !(state inside {START, DATA, END})
                   |=> (state == END && tx == 1));

  // START state behavior at a baud tick
  assert property (baud_edge && state == START |-> (tx == 0 && data_counter == 0) ##1 state == DATA);

  // DATA state drives bit from data_reg indexed by data_counter
  assert property (baud_edge && state == DATA |-> tx == data_reg[data_counter]);

  // DATA state progression and wrap to END
  assert property (baud_edge && state == DATA && data_counter != 7
                   |=> (state == DATA && data_counter == $past(data_counter) + 1));
  assert property (baud_edge && state == DATA && data_counter == 7
                   |=> (state == END && data_counter == 0));

  // END (idle) drives stop/high at baud tick
  assert property (baud_edge && state == END |-> tx == 1);

  // data_accepted only when accepting at END on a baud tick with data_ready
  assert property (data_accepted |-> (baud_edge && state == END && data_ready));

  // Acceptance loads data_reg and moves to START next cycle
  assert property (baud_edge && state == END && data_ready
                   |-> data_accepted ##1 (state == START && data_reg == $past(data)));

  // After an acceptance, we see a START tick, 8 DATA ticks, then an END tick (all on baud edges), allowing gaps between baud edges
  sequence be_start;  ##[1:$] (baud_edge && state == START && tx == 0); endsequence
  sequence be_data;   ##[1:$] (baud_edge && state == DATA);             endsequence
  sequence be_end;    ##[1:$] (baud_edge && state == END);              endsequence
  assert property ((baud_edge && state == END && data_ready)
                   |-> be_start ##0 be_data[*8] ##0 be_end);

  // Coverage
  cover property (baud_edge && state == END && data_ready);                  // handshake observed
  cover property ( (baud_edge && state == END && data_ready)
                   ##0 be_start ##0 be_data[*8] ##0 be_end );                // full frame
  cover property ( (baud_edge && !(state inside {START, DATA, END})) ##1 (state == END) ); // illegal-state recovery
  cover property ( (baud_edge && state == END && data_ready)
                   ##[1:$] (baud_edge && state == END && data_ready) );     // back-to-back frames
endmodule

bind UART_TX UART_TX_sva u_uart_tx_sva();