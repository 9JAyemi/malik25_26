// SVA for Profibus
// Bind this checker to the DUT:
// bind Profibus Profibus_assertions asrt (.*);

module Profibus_assertions (
  input clk,
  input rst,
  input [7:0] din_master,
  input [7:0] din_slave,
  input [7:0] dout_master,
  input [7:0] dout_slave,
  input       status_master,
  input       status_slave,
  input [1:0] state_master,
  input [1:0] state_slave,
  input [7:0] cmd_master,
  input [7:0] cmd_slave,
  input [7:0] data_master,
  input [7:0] data_slave
);
  localparam IDLE         = 2'b00;
  localparam SEND_CMD     = 2'b01;
  localparam RECEIVE_DATA = 2'b10;
  localparam SEND_DATA    = 2'b11;

  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Reset behavior (synchronous reset asserted)
  assert property (@cb rst |-> (state_master==IDLE && dout_slave==8'h00));
  assert property (@cb rst |-> (state_slave ==IDLE && dout_master==8'h00));

  // Legal encodings
  assert property (@cb state_master inside {IDLE,SEND_CMD,RECEIVE_DATA,SEND_DATA});
  assert property (@cb state_slave  inside {IDLE,SEND_CMD,RECEIVE_DATA,SEND_DATA});

  // Status reflects IDLE
  assert property (@cb status_master == (state_master==IDLE));
  assert property (@cb status_slave  == (state_slave==IDLE));

  // Master FSM transitions and datapath
  assert property (@cb (state_master==IDLE && din_master!=8'h00) |=> (state_master==SEND_CMD && cmd_master==$past(din_master)));
  assert property (@cb (state_master==IDLE && din_master==8'h00) |=> state_master==IDLE);

  assert property (@cb state_master==SEND_CMD |=> (state_master==RECEIVE_DATA && dout_slave==$past(cmd_master)));

  assert property (@cb (state_master==RECEIVE_DATA && din_master!=8'h00) |=> (state_master==SEND_DATA && data_master==$past(din_master)));
  assert property (@cb (state_master==RECEIVE_DATA && din_master==8'h00) |=> state_master==RECEIVE_DATA);

  assert property (@cb state_master==SEND_DATA |=> (state_master==IDLE && dout_slave==$past(data_master)));

  // Slave FSM transitions and datapath
  assert property (@cb (state_slave==IDLE && din_slave!=8'h00) |=> (state_slave==RECEIVE_DATA && cmd_slave==$past(din_slave)));
  assert property (@cb (state_slave==IDLE && din_slave==8'h00) |=> state_slave==IDLE);

  assert property (@cb state_slave==RECEIVE_DATA |=> (state_slave==SEND_DATA && dout_master==$past(cmd_slave)));

  assert property (@cb (state_slave==SEND_DATA && din_slave!=8'h00) |=> (state_slave==IDLE && data_slave==$past(din_slave)));
  assert property (@cb (state_slave==SEND_DATA && din_slave==8'h00) |=> state_slave==SEND_DATA);

  // Write-only-in-expected-states (stability elsewhere)
  assert property (@cb $changed(dout_slave)  |-> $past(state_master inside {SEND_CMD,SEND_DATA}));
  assert property (@cb $changed(dout_master) |-> $past(state_slave==RECEIVE_DATA));

  assert property (@cb $changed(cmd_master)  |-> $past(state_master==IDLE && din_master!=8'h00));
  assert property (@cb $changed(data_master) |-> $past(state_master==RECEIVE_DATA && din_master!=8'h00));
  assert property (@cb $changed(cmd_slave)   |-> $past(state_slave==IDLE && din_slave!=8'h00));
  assert property (@cb $changed(data_slave)  |-> $past(state_slave==SEND_DATA && din_slave!=8'h00));

  // Functional coverage
  cover property (@cb state_master==IDLE ##1 state_master==SEND_CMD ##1 state_master==RECEIVE_DATA ##1 state_master==SEND_DATA ##1 state_master==IDLE);
  cover property (@cb state_slave==IDLE  ##1 state_slave==RECEIVE_DATA ##1 state_slave==SEND_DATA ##1 state_slave==IDLE);

  cover property (@cb (state_master==SEND_CMD, dout_slave==cmd_master));
  cover property (@cb (state_master==SEND_DATA, dout_slave==data_master));
  cover property (@cb (state_slave==RECEIVE_DATA, dout_master==cmd_slave));
endmodule