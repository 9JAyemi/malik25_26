// SVA for Profibus
module Profibus_sva #(parameter int W=8)
(
  input  logic              clk,
  input  logic              rst,
  input  logic [W-1:0]      data_in,
  input  logic [W-1:0]      data_out,
  input  logic              enable,
  input  logic              busy,
  input  logic [1:0]        state,
  input  logic [W-1:0]      master_data_out,
  input  logic              master_enable,
  input  logic              master_busy,
  input  logic [W-1:0]      slave_data_in,
  input  logic [W-1:0]      slave_data_out,
  input  logic              slave_enable,
  input  logic              slave_busy
);

  localparam logic [1:0] IDLE=2'b00, SEND=2'b01, RECEIVE=2'b10;

  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // X/validity
  assert property (!$isunknown(state));
  assert property (state inside {IDLE,SEND,RECEIVE});
  assert property (!$isunknown({enable,busy,master_enable,master_busy,slave_enable,slave_busy}));
  assert property (!$isunknown({master_data_out,slave_data_in,slave_data_out,data_out}));

  // Reset behavior
  assert property (rst |-> state==IDLE);
  assert property (rst |-> !enable && !busy && master_data_out=={W{1'b0}} && slave_data_out=={W{1'b0}});

  // Output/enable/busy definitions
  assert property (enable == (state==SEND));
  assert property (master_enable == (state==SEND));
  assert property (busy == (state inside {SEND,RECEIVE}));
  assert property (master_busy == busy);
  assert property (slave_busy  == busy);
  assert property (slave_enable == (state==RECEIVE));

  // Datapath relationships
  assert property ((state==SEND)  |-> master_data_out == data_in);
  assert property ((state!=SEND)  |-> master_data_out == {W{1'b0}});
  assert property (slave_data_in == master_data_out);
  assert property (data_out == (state==RECEIVE ? master_data_out : {W{1'b0}}));
  assert property ((state!=RECEIVE) |-> data_out == {W{1'b0}});

  // FSM next-state behavior (as coded)
  assert property ((state==IDLE  && !enable)     |=> state==IDLE);
  assert property ((state==IDLE  &&  enable)     |=> state==SEND);
  assert property ((state==SEND  &&  master_busy)|=> state==SEND);
  assert property ((state==SEND  && !master_busy)|=> state==RECEIVE);
  assert property ((state==RECEIVE && slave_busy)|=> state==RECEIVE);
  assert property ((state==RECEIVE && !slave_busy)|=> state==IDLE);

  // Coverage
  cover property (state==IDLE);
  cover property (state==SEND);
  cover property (state==RECEIVE);
  cover property (state==IDLE ##1 state==SEND ##1 state==RECEIVE ##1 state==IDLE);
  cover property ((state==IDLE && enable) ##1 state==SEND);
  cover property ((state==SEND && !master_busy) ##1 state==RECEIVE);
  cover property ((state==RECEIVE && !slave_busy) ##1 state==IDLE);

endmodule

bind Profibus Profibus_sva #(.W(8)) u_profibus_sva (
  .clk(clk),
  .rst(rst),
  .data_in(data_in),
  .data_out(data_out),
  .enable(enable),
  .busy(busy),
  .state(state),
  .master_data_out(master_data_out),
  .master_enable(master_enable),
  .master_busy(master_busy),
  .slave_data_in(slave_data_in),
  .slave_data_out(slave_data_out),
  .slave_enable(slave_enable),
  .slave_busy(slave_busy)
);