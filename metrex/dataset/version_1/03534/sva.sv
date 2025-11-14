// SVA checker for uart_light_tx_ctrl
module uart_light_tx_ctrl_sva
#(
  parameter STATE_COUNT = 2,
  parameter [STATE_COUNT-1:0] IDLE = 2'b00,
  parameter [STATE_COUNT-1:0] LOAD = 2'b01,
  parameter [STATE_COUNT-1:0] TRANSMITTING = 2'b10
)(
  input  wire reset,
  input  wire clk_tx,

  // DUT ports
  input  wire word_ready,
  input  wire fifo_tx_full,
  input  wire fifo_tx_empty,
  input  wire frame_done,
  input  wire transmit,
  input  wire clear,
  input  wire fifo_read_enable,
  input  wire fifo_full,
  input  wire fifo_empty,
  input  wire fifo_write_enable,

  // Internal state tap
  input  wire [STATE_COUNT-1:0] state_cur
);

  default clocking cb @(posedge clk_tx); endclocking

  // Async reset forces IDLE synchronously to clk edge
  assert property (@(posedge clk_tx) reset |-> state_cur == IDLE)
    else $error("state_cur not IDLE during reset");

  // State encoding legal
  assert property (disable iff (reset) (state_cur inside {IDLE, LOAD, TRANSMITTING}))
    else $error("Illegal state encoding");

  // Next-state transitions
  assert property (disable iff (reset) (state_cur == IDLE && !fifo_empty) |=> state_cur == LOAD)
    else $error("IDLE->LOAD transition missing when fifo not empty");

  assert property (disable iff (reset) (state_cur == IDLE && fifo_empty) |=> state_cur == IDLE)
    else $error("IDLE should hold when fifo empty");

  assert property (disable iff (reset) (state_cur == LOAD) |=> state_cur == TRANSMITTING)
    else $error("LOAD must go to TRANSMITTING");

  assert property (disable iff (reset) (state_cur == TRANSMITTING && frame_done) |=> state_cur == IDLE)
    else $error("TRANSMITTING->IDLE on frame_done");

  assert property (disable iff (reset) (state_cur == TRANSMITTING && !frame_done) |=> state_cur == TRANSMITTING)
    else $error("TRANSMITTING should hold while !frame_done");

  // Output decode equivalences
  assert property (disable iff (reset) fifo_read_enable == (state_cur == LOAD))
    else $error("fifo_read_enable must be 1 only in LOAD");

  assert property (disable iff (reset) transmit == (state_cur == TRANSMITTING && !frame_done))
    else $error("transmit decode mismatch");

  assert property (disable iff (reset) clear == (state_cur == TRANSMITTING && frame_done))
    else $error("clear decode mismatch");

  // Mutual exclusion
  assert property (disable iff (reset) !(transmit && clear))
    else $error("transmit and clear must not be high together");

  // Pass-throughs and write-enable logic
  assert property (@(posedge clk_tx) fifo_tx_full  == fifo_full)
    else $error("fifo_tx_full must mirror fifo_full");

  assert property (@(posedge clk_tx) fifo_tx_empty == fifo_empty)
    else $error("fifo_tx_empty must mirror fifo_empty");

  assert property (@(posedge clk_tx) fifo_write_enable == (word_ready && !fifo_full))
    else $error("fifo_write_enable equation mismatch");

  // No X/Z on key signals after reset
  assert property (disable iff (reset)
                   !$isunknown({state_cur, transmit, clear, fifo_read_enable,
                                fifo_tx_full, fifo_tx_empty, fifo_write_enable}))
    else $error("Unknown (X/Z) detected on key signals");

  // Coverage
  cover property (disable iff (reset)
                  (state_cur==IDLE && !fifo_empty)
                  ##1 state_cur==LOAD
                  ##1 state_cur==TRANSMITTING && !frame_done
                  ##1 state_cur==TRANSMITTING && frame_done
                  ##1 state_cur==IDLE);

  cover property (disable iff (reset) state_cur==TRANSMITTING && !frame_done && transmit);
  cover property (disable iff (reset) state_cur==TRANSMITTING && frame_done && clear);
  cover property (@(posedge clk_tx) word_ready && !fifo_full && fifo_write_enable);

endmodule

// Bind into DUT (adjust if you prefer explicit connections)
bind uart_light_tx_ctrl
  uart_light_tx_ctrl_sva #(.STATE_COUNT(STATE_COUNT),
                           .IDLE(IDLE),
                           .LOAD(LOAD),
                           .TRANSMITTING(TRANSMITTING))
  uart_light_tx_ctrl_sva_i (
    .reset(reset),
    .clk_tx(clk_tx),
    .word_ready(word_ready),
    .fifo_tx_full(fifo_tx_full),
    .fifo_tx_empty(fifo_tx_empty),
    .frame_done(frame_done),
    .transmit(transmit),
    .clear(clear),
    .fifo_read_enable(fifo_read_enable),
    .fifo_full(fifo_full),
    .fifo_empty(fifo_empty),
    .fifo_write_enable(fifo_write_enable),
    .state_cur(state_cur)
  );