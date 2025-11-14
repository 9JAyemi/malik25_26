// SVA for uart_transmitter
module uart_transmitter_sva (input logic clk, input logic rst);
  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Past-valid guard for $past usage
  logic past_valid;
  always_ff @(posedge clk) past_valid <= !rst;

  // Reset behavior
  assert property (@(posedge clk) rst |=> (shift_reg==10'b0 && bit_count==4'd0 && start_bit==1'b0 && stop_bit==1'b1));

  // Invariants
  assert property (bit_count inside {4'd0,4'd1,4'd2});
  assert property (tx == shift_reg[0]);
  assert property (!rst |-> (start_bit==1'b0 && stop_bit==1'b1));

  // bit_count transitions
  assert property ((bit_count==4'd0) |=> (bit_count==4'd1));
  assert property ((bit_count==4'd1) |=> (bit_count==4'd2));
  assert property ((bit_count==4'd2) |=> (bit_count==4'd0));

  // shift_reg updates
  assert property (past_valid && bit_count==4'd0 |=> shift_reg == {start_bit, $past(data_in), stop_bit});
  assert property (past_valid && bit_count==4'd1 |=> shift_reg == {$past(shift_reg)[8:0], 1'b0});
  assert property (past_valid && bit_count==4'd2 |=> shift_reg == {$past(shift_reg)[8:0], 1'b1});

  // Basic coverage
  cover property (bit_count==4'd0 ##1 bit_count==4'd1 ##1 bit_count==4'd2 ##1 bit_count==4'd0);
  cover property (past_valid && bit_count==4'd1 ##1 shift_reg[0]==1'b0);
  cover property (past_valid && bit_count==4'd2 ##1 shift_reg[0]==1'b1);
endmodule

bind uart_transmitter uart_transmitter_sva u_tx_sva(.clk(clk), .rst(rst));


// SVA for uart_receiver
module uart_receiver_sva (input logic clk, input logic rst);
  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Past-valid guard for $past usage
  logic past_valid;
  always_ff @(posedge clk) past_valid <= !rst;

  // Reset behavior
  assert property (@(posedge clk) rst |=> (shift_reg==10'b0 && bit_count==4'd0 && start_bit==1'b0 && stop_bit==1'b0 && data_out==8'b0));

  // Invariants
  assert property (bit_count inside {4'd0,4'd1,4'd2});

  // bit_count transitions and state updates
  assert property (past_valid && (bit_count==4'd0) |=> (start_bit==$past(rx) && bit_count==4'd1));
  assert property (past_valid && (bit_count==4'd1) |=> (shift_reg=={$past(shift_reg)[8:0], $past(rx)} && bit_count==4'd2));
  assert property (past_valid && (bit_count==4'd2) |=> (stop_bit==$past(rx) && data_out==$past(shift_reg)[8:1] && bit_count==4'd0));

  // Basic coverage
  cover property (bit_count==4'd0 ##1 bit_count==4'd1 ##1 bit_count==4'd2 ##1 bit_count==4'd0);
  cover property (past_valid && bit_count==4'd2 ##1 $changed(data_out));
endmodule

bind uart_receiver uart_receiver_sva u_rx_sva(.clk(clk), .rst(rst));