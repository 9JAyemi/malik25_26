// SVA for rfid. Bind this checker to the DUT.
module rfid_sva (
  input logic        clk,
  input logic [7:0]  tx_data,
  input logic        tx_en,
  input logic        rx_en,
  input logic [7:0]  rx_data,
  input logic [1:0]  tx_mod
);
  default clocking cb @(posedge clk); endclocking

  bit past_valid; initial past_valid = 0;
  always_ff @(posedge clk) past_valid <= 1'b1;

  // Transmitter encoding: forward (inputs -> next tx_mod)
  assert property (disable iff(!past_valid) ( tx_en &&  tx_data[0]) |=> (tx_mod == 2'b11));
  assert property (disable iff(!past_valid) ( tx_en && !tx_data[0]) |=> (tx_mod == 2'b01));
  assert property (disable iff(!past_valid) (!tx_en)               |=> (tx_mod == 2'b00));

  // Transmitter encoding: legal/consistent coding
  assert property (disable iff(!past_valid) (tx_mod inside {2'b00,2'b01,2'b11}));
  assert property (disable iff(!past_valid) (tx_mod == 2'b11) |-> $past(tx_en &&  tx_data[0]));
  assert property (disable iff(!past_valid) (tx_mod == 2'b01) |-> $past(tx_en && !tx_data[0]));
  assert property (disable iff(!past_valid) (tx_mod == 2'b00) |-> $past(!tx_en));

  // Receiver behavior: next rx_data based on current rx_en/tx_mod
  assert property (disable iff(!past_valid) (rx_en && (tx_mod == 2'b11)) |=> (rx_data == 8'hFF));
  assert property (disable iff(!past_valid) (rx_en && (tx_mod != 2'b11)) |=> (rx_data == $past(tx_data)));
  // Hold when rx_en low
  assert property (disable iff(!past_valid) (!rx_en) |=> (rx_data == $past(rx_data)));

  // Coverage
  cover property (past_valid && tx_en &&  tx_data[0] ##1 (tx_mod == 2'b11));
  cover property (past_valid && tx_en && !tx_data[0] ##1 (tx_mod == 2'b01));
  cover property (past_valid && !tx_en             ##1 (tx_mod == 2'b00));

  cover property (past_valid && rx_en && (tx_mod == 2'b11) ##1 (rx_data == 8'hFF));
  cover property (past_valid && rx_en && (tx_mod != 2'b11) ##1 (rx_data == $past(tx_data)));
  cover property (past_valid && !rx_en ##1 $stable(rx_data));
endmodule

bind rfid rfid_sva i_rfid_sva (
  .clk(clk),
  .tx_data(tx_data),
  .tx_en(tx_en),
  .rx_en(rx_en),
  .rx_data(rx_data),
  .tx_mod(tx_mod)
);