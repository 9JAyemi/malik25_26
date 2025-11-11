// SVA for profibus_slave and profibus_master
// Focused, concise, high-quality checks and coverage

// ---------- Slave SVA ----------
module profibus_slave_sva (
  input clk,
  input rst,
  input enable,
  input req,
  input [7:0] data_in,
  input ack,
  input [7:0] data_out,
  input [7:0] internal_data
);
  default clocking cb @(posedge clk); endclocking

  // Combinational correctness
  assert property (cb ack == (enable && req));

  // Reset clears storage and output
  assert property (cb rst |-> (internal_data==8'h00 && data_out==8'h00));

  // Load on request, reflect on output next cycle
  assert property (cb disable iff (rst)
                   (enable && req) |=> (internal_data==$past(data_in) && data_out==$past(data_in)));

  // Hold when no load
  assert property (cb disable iff (rst)
                   !(enable && req) |=> ($stable(internal_data) && $stable(data_out)));

  // Output mirrors storage
  assert property (cb data_out == internal_data);

  // No X/Z on key outputs
  assert property (cb disable iff (rst) !$isunknown({ack, data_out, internal_data}));

  // Coverage
  cover property (cb disable iff (rst) (enable && req && data_in!=8'h00)
                               ##1 (data_out==$past(data_in)));
  cover property (cb disable iff (rst) (!(enable && req)) ##1 $stable(data_out));
endmodule

bind profibus_slave profibus_slave_sva slave_sva (
  .clk(clk), .rst(rst), .enable(enable), .req(req),
  .data_in(data_in), .ack(ack), .data_out(data_out),
  .internal_data(internal_data)
);

// ---------- Master SVA ----------
module profibus_master_sva #(
  parameter IDLE      = 3'b000,
  parameter SEND_REQ  = 3'b001,
  parameter WAIT_ACK  = 3'b010,
  parameter READ_DATA = 3'b011
) (
  input clk,
  input rst,
  input enable,
  input req,
  input ack,
  input [7:0] data_in,
  input [7:0] data_out,
  input [2:0] state
);
  default clocking cb @(posedge clk); endclocking

  // Reset state/output
  assert property (cb rst |-> (state==IDLE && req==1'b0));

  // Gating: hold when not enabled
  assert property (cb disable iff (rst) !enable |=> $stable({state, req, data_out}));

  // Legal state encodings only
  assert property (cb disable iff (rst) state inside {IDLE, SEND_REQ, WAIT_ACK, READ_DATA});

  // IDLE behavior with no data
  assert property (cb disable iff (rst)
                   (enable && state==IDLE && data_in==8'h00) |=> (state==IDLE && req==1'b0));

  // SEND_REQ -> WAIT_ACK, req asserted
  assert property (cb disable iff (rst)
                   (enable && state==SEND_REQ) |=> (state==WAIT_ACK && req==1'b1));

  // WAIT_ACK holds until ack, req stays high
  assert property (cb disable iff (rst)
                   (enable && state==WAIT_ACK && !ack) |=> (state==WAIT_ACK && req==1'b1));
  assert property (cb disable iff (rst)
                   (enable && state==WAIT_ACK && ack) |=> state==READ_DATA);

  // READ_DATA -> IDLE and deassert req
  assert property (cb disable iff (rst)
                   (enable && state==READ_DATA) |=> (state==IDLE && req==1'b0));

  // data_out may change only in READ_DATA
  assert property (cb disable iff (rst) $changed(data_out) |-> (state==READ_DATA && enable));

  // End-to-end transaction: capture data_in in IDLE, propagate to data_out in READ_DATA
  property p_txn;
    automatic logic [7:0] din;
    (enable && state==IDLE && data_in!=8'h00, din=data_in)
    |=> (state==SEND_REQ && req)
    ##1 (state==WAIT_ACK && req)
    ##[0:$] (state==WAIT_ACK && req && !ack)
    ##1 (state==WAIT_ACK && ack)
    ##1 (state==READ_DATA && data_out==din)
    ##1 (state==IDLE && !req);
  endproperty
  assert property (cb disable iff (rst) p_txn);

  // No X/Z on key outputs/state
  assert property (cb disable iff (rst) !$isunknown({req, data_out, state}));

  // Coverage
  cover property (cb disable iff (rst)
    (enable && state==IDLE && data_in!=8'h00)
    ##1 state==SEND_REQ
    ##1 (state==WAIT_ACK && !ack)
    ##1 (state==WAIT_ACK && !ack)
    ##1 (state==WAIT_ACK && ack)
    ##1 state==READ_DATA
    ##1 state==IDLE);

  cover property (cb disable iff (rst)
    (enable && state==IDLE && data_in!=8'h00)
    ##1 state==SEND_REQ
    ##1 (state==WAIT_ACK && ack)
    ##1 state==READ_DATA
    ##1 state==IDLE);

  cover property (cb disable iff (rst)
    (enable && state==IDLE && data_in==8'h00)[*3]);
endmodule

bind profibus_master profibus_master_sva master_sva (
  .clk(clk), .rst(rst), .enable(enable),
  .req(req), .ack(ack), .data_in(data_in), .data_out(data_out),
  .state(state)
);