// SVA for uart_transmitter and uart_receiver
// Bind these to the DUTs. Concise, high-coverage checks.

`ifndef UART_SVA
`define UART_SVA

// ----------------------- Transmitter SVA -----------------------
module uart_tx_sva (
  input logic clk, rst,
  input logic [7:0] data_in,
  input logic start,
  input logic tx, done,
  input logic [3:0] counter
);
  // Sample data at start accept
  logic [7:0] din;
  wire idle = (counter==4'd0);
  wire busy = !idle;

  always @(posedge clk) if (!rst && start && idle) din <= data_in;

  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Reset behavior
  assert property (@(posedge clk) rst |-> counter==4'd0 && tx==1'b1 && done==1'b0);

  // Accept start only from idle; immediate next-state
  assert property (start && idle |=> counter==4'd1 && done==1'b0);

  // Idle line high
  assert property (idle |-> tx==1'b1);

  // Busy counter monotonic and no early done
  assert property (busy && counter inside {[4'd1:4'd9]} |=> counter==$past(counter)+4'd1 && done==1'b0);

  // Frame completes at count 10 -> reset and done
  assert property ($past(busy) && $past(counter)==4'd10 |-> counter==4'd0 && done==1'b1);

  // done implies stop-bit on line
  assert property (done |-> tx==1'b1);

  // Start while busy is ignored (no restart)
  assert property (busy && (counter inside {[4'd1:4'd9]}) && start |=> counter==$past(counter)+4'd1);

  // Full serialization: 1 start(0), 8 data LSB->MSB, 1 stop(1) with done
  assert property (
    start && idle |=> ##1 (tx==1'b0)
                    ##1 (tx==din[0])
                    ##1 (tx==din[1])
                    ##1 (tx==din[2])
                    ##1 (tx==din[3])
                    ##1 (tx==din[4])
                    ##1 (tx==din[5])
                    ##1 (tx==din[6])
                    ##1 (tx==din[7])
                    ##1 (tx==1'b1 && done)
  );

  // Coverage: full frame completes in 10 cycles
  cover property (start && idle ##10 done);

endmodule

bind uart_transmitter uart_tx_sva tx_sva_bind (
  .clk(clk), .rst(rst),
  .data_in(data_in),
  .start(start),
  .tx(tx), .done(done),
  .counter(counter)
);


// ----------------------- Receiver SVA -----------------------
module uart_rx_sva (
  input logic clk, rst,
  input logic rx,
  input logic [7:0] data_out,
  input logic valid,
  input logic [3:0] counter,
  input logic [9:0] shift_reg,
  input logic waiting_for_start
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Reset behavior
  assert property (@(posedge clk) rst |-> counter==4'd0 && waiting_for_start && valid==1'b0);

  // While waiting, counter holds 0 and valid stays 0
  assert property (waiting_for_start |-> counter==4'd0 && valid==1'b0);

  // Start detect: low rx exits waiting and sets counter=1
  assert property (waiting_for_start && (rx==1'b0) |=> !waiting_for_start && counter==4'd1);

  // Busy: counter increments, valid low until end
  assert property (!waiting_for_start && counter inside {[4'd1:4'd9]} |=> counter==$past(counter)+4'd1 && valid==1'b0);

  // End-of-frame: when counter hits 10 (previous cycle), next cycle returns to waiting,
  // outputs reflect previous shift_reg contents
  assert property ($past(!waiting_for_start) && $past(counter)==4'd10 |-> waiting_for_start && counter==4'd0
                   && valid==$past(shift_reg[9])
                   && data_out==$past(shift_reg[8:1]));

  // Valid only when idle-after-frame
  assert property (valid |-> waiting_for_start && counter==4'd0);

  // Coverage: detect start to valid
  cover property (waiting_for_start && (rx==1'b0) ##10 valid);

endmodule

bind uart_receiver uart_rx_sva rx_sva_bind (
  .clk(clk), .rst(rst),
  .rx(rx),
  .data_out(data_out),
  .valid(valid),
  .counter(counter),
  .shift_reg(shift_reg),
  .waiting_for_start(waiting_for_start)
);

`endif