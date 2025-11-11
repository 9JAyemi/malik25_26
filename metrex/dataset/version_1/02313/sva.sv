// SVA checker for uart_rx
module uart_rx_sva (
  input logic        clk,
  input logic        reset,
  input logic        rxd,
  input logic        ack,
  input logic [7:0]  rx_data,
  input logic        rx_full,
  input logic [1:0]  state,
  input logic [2:0]  bit_count,
  input logic [7:0]  data_bits,
  input logic        stop_bit
);
  localparam IDLE  = 2'd0;
  localparam START = 2'd1;
  localparam DATA  = 2'd2;
  localparam STOP  = 2'd3;

  // No X on key signals
  assert property (@(posedge clk) !$isunknown({rxd, state, bit_count, stop_bit, ack, rx_full, rx_data}));

  // Reset behavior
  assert property (@(posedge clk) reset |-> (state==IDLE && bit_count==3'd0 && data_bits==8'd0 && stop_bit==1'b1 && rx_full==1'b0));

  // Legal state encodings
  assert property (@(posedge clk) disable iff (reset) state inside {IDLE,START,DATA,STOP});

  // IDLE behavior
  assert property (@(posedge clk) disable iff (reset) (state==IDLE && rxd) |=> state==IDLE);
  assert property (@(posedge clk) disable iff (reset)
                   ($past(state)==IDLE && state==START) |-> ($past(!rxd) && bit_count==3'd0 && data_bits==8'd0 && stop_bit==1'b1));

  // START progress (should not livelock)
  assert property (@(posedge clk) disable iff (reset) (state==START) |-> ##[1:12] (state==DATA));

  // START bit sampling for bit_count 1..7
  assert property (@(posedge clk) disable iff (reset)
                   ($past(state)==START && $past(bit_count) inside {[3'd1:3'd7]})
                   |-> data_bits[$past(bit_count)-1] == $past(rxd));

  // DATA progress (should reach STOP)
  assert property (@(posedge clk) disable iff (reset) (state==DATA) |-> ##[1:9] (state==STOP));

  // DATA bit sampling for bit_count 0..7
  assert property (@(posedge clk) disable iff (reset)
                   ($past(state)==DATA && $past(bit_count) inside {[3'd0:3'd7]})
                   |-> data_bits[$past(bit_count)] == $past(rxd));

  // STOP outputs correctness at decision point
  assert property (@(posedge clk) disable iff (reset)
                   (state==STOP && bit_count==3'd0)
                   |-> (ack == (rxd==stop_bit) &&
                        rx_full == (rxd==stop_bit) &&
                        (rx_data == ((rxd==stop_bit) ? data_bits : 8'h00))));

  // STOP must return to IDLE next cycle
  assert property (@(posedge clk) disable iff (reset) (state==STOP && bit_count==3'd0) |=> state==IDLE);

  // Outputs only update at STOP decision (outside reset)
  assert property (@(posedge clk) disable iff (reset)
                   !(state==STOP && bit_count==3'd0) |=> (ack==$past(ack) && rx_full==$past(rx_full) && rx_data==$past(rx_data)));

  // Ack implies full
  assert property (@(posedge clk) disable iff (reset) ack |-> rx_full);

  // Transition intent checks (document spec vs implementation)
  assert property (@(posedge clk) disable iff (reset)
                   ($past(state)==START && state==DATA) |-> ($past(bit_count) > 9));
  assert property (@(posedge clk) disable iff (reset)
                   ($past(state)==DATA && state==STOP) |-> ($past(bit_count) >= 8));

  // Coverage: successful frame
  cover property (@(posedge clk) disable iff (reset)
                  (state==IDLE && !rxd)
                  ##1 state==START
                  ##[1:12] state==DATA
                  ##[1:9] (state==STOP && bit_count==3'd0 && rxd==stop_bit)
                  ##1 (ack && rx_full)
                  ##1 state==IDLE);

  // Coverage: stop-bit error path
  cover property (@(posedge clk) disable iff (reset)
                  state==START
                  ##[1:12] state==DATA
                  ##[1:9] (state==STOP && bit_count==3'd0 && rxd!=stop_bit)
                  ##1 (!ack && !rx_full)
                  ##1 state==IDLE);
endmodule

// Bind SVA to DUT
bind uart_rx uart_rx_sva u_uart_rx_sva (
  .clk(clk),
  .reset(reset),
  .rxd(rxd),
  .ack(ack),
  .rx_data(rx_data),
  .rx_full(rx_full),
  .state(state),
  .bit_count(bit_count),
  .data_bits(data_bits),
  .stop_bit(stop_bit)
);