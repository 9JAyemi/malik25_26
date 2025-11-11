// SVA for modbus. Bind to DUT; no DUT/testbench changes required.

module modbus_sva #(parameter int is_master = 1)(
  input logic        clk,
  input logic        rst,
  input logic        en,
  input logic [7:0]  addr,
  input logic [7:0]  data_in,
  input logic [7:0]  data_out,
  input logic        done,
  input logic [2:0]  state,
  input logic [7:0]  response,
  input logic [7:0]  request,
  input logic [7:0]  reg_data
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Reset behavior (synchronous)
  assert property (@cb rst |-> (state==3'd0 && done==1'b0));

  // Gating by en: state and key regs stable when en=0
  assert property (@cb !en |-> $stable(state));
  assert property (@cb !en |-> $stable(done));
  assert property (@cb !en |-> $stable(response));
  assert property (@cb !en |-> $stable(request));
  assert property (@cb !en |-> $stable(reg_data));

  // data_out mirrors response
  assert property (@cb data_out == response);

  // State encoding stays within 0..3
  assert property (@cb state inside {3'd0,3'd1,3'd2,3'd3});

  // Master FSM sequencing and effects
  assert property (@cb (is_master && en && state==3'd0) |=> state==3'd1);
  assert property (@cb (is_master && en && state==3'd1) |=> state==3'd2);
  assert property (@cb (is_master && en && state==3'd2) |=> state==3'd3);
  assert property (@cb (is_master && en && state==3'd3) |=> (state==3'd0 && done && response==$past(data_in)));

  // Master request register (truncation of concat in RTL -> equals previous reg_data)
  assert property (@cb (is_master && en && state==3'd0) |=> request == $past(reg_data));

  // Slave behavior
  assert property (@cb (!is_master && en && state==3'd1) |=> (state==3'd0 && done && response==$past(reg_data)));
  assert property (@cb (!is_master && en && state==3'd2) |=> (state==3'd0));
  assert property (@cb (!is_master && en && state==3'd3) |=> (state==3'd0 && done && response==$past(reg_data) && reg_data==$past(data_in)));

  // done rises only from defined source states
  assert property (@cb $rose(done) && is_master  |-> $past(en && state==3'd3 && is_master));
  assert property (@cb $rose(done) && !is_master |-> $past(en && (state==3'd1 || state==3'd3) && !is_master));

  // Coverage
  cover property (@cb is_master && !rst ##1 en && state==3'd0 ##1 en && state==3'd1 ##1 en && state==3'd2 ##1 en && state==3'd3 ##1 done);
  cover property (@cb !is_master && en && state==3'd1 ##1 done);
  cover property (@cb !is_master && en && state==3'd3 ##1 done);

endmodule

// Bind example (binds to all modbus instances)
bind modbus modbus_sva #(.is_master(is_master)) modbus_sva_i (
  .clk(clk),
  .rst(rst),
  .en(en),
  .addr(addr),
  .data_in(data_in),
  .data_out(data_out),
  .done(done),
  .state(state),
  .response(response),
  .request(request),
  .reg_data(reg_data)
);