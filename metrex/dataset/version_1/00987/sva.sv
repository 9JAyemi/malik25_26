// SVA for rcn_master_slave
// Bind this module to the DUT. Focused, reset-safe, and full functional coverage of key behaviors.
module rcn_master_slave_sva #(
  parameter int MASTER_ID = 0,
  parameter int ADDR_MASK = 0,
  parameter int ADDR_BASE = 1
)(
  input  logic         rst,
  input  logic         clk,

  input  logic [68:0]  rcn_in,
  output logic [68:0]  rcn_out,

  input  logic         cs,
  input  logic  [1:0]  seq,
  output logic         busy,
  input  logic         wr,
  input  logic  [3:0]  mask,
  input  logic [23:0]  addr,
  input  logic [31:0]  wdata,

  output logic         rdone,
  output logic         wdone,
  output logic  [1:0]  rsp_seq,
  output logic  [3:0]  rsp_mask,
  output logic [23:0]  rsp_addr,
  output logic [31:0]  rsp_data,

  output logic         slave_cs,
  output logic         slave_wr,
  output logic  [3:0]  slave_mask,
  output logic [23:0]  slave_addr,
  output logic [31:0]  slave_wdata,
  input  logic [31:0]  slave_rdata
);

  // Past-valid tracking for $past depth 1/2
  logic past1, past2;
  always_ff @(posedge clk or posedge rst) begin
    if (rst) begin past1 <= 1'b0; past2 <= 1'b0; end
    else begin past1 <= 1'b1; past2 <= past1; end
  end

  localparam logic [5:0]  my_id   = MASTER_ID[5:0];
  localparam logic [23:0] my_mask = ADDR_MASK[23:0];
  localparam logic [23:0] my_base = ADDR_BASE[23:0];

  // Helpers (use sampled flits: rin0 = $past(rcn_in), rin1 = $past(rcn_in,2))
  let rin0 = $past(rcn_in);
  let rin1 = $past(rcn_in,2);
  let MY_REQ_ON(in)  = in[68] && in[67] && (((in[55:34]) & my_mask[23:2]) == my_base[23:2]);
  let MY_RESP_ON(in) = in[68] && !in[67] && (in[65:60] == my_id);

  let MY_REQ_NOW  = MY_REQ_ON(rin0);   // combinational request seen at slave side
  let MY_REQ_D1   = MY_REQ_ON(rin1);   // pipelined one cycle for response inject
  let MY_RESP_NOW = MY_RESP_ON(rin1);  // response targeted to me at output stage
  let CAN_INJECT  = cs && !(rin1[68] && !MY_RESP_NOW); // same as req_valid

  // Default clocking
  default clocking cb @(posedge clk); endclocking

  // Reset sanity
  assert property (rst |-> (rcn_out == 69'd0 && !busy && !slave_cs && !rdone && !wdone));

  // Busy/req_valid gating (req_valid == CAN_INJECT)
  assert property (disable iff (rst) past2 |-> busy == (rin1[68] && !MY_RESP_NOW));
  assert property (disable iff (rst) past2 && CAN_INJECT |-> !busy);
  assert property (disable iff (rst) past2 && busy |-> !CAN_INJECT);

  // Slave side decodes current incoming flit (rin0)
  assert property (disable iff (rst) past1 |-> slave_cs == MY_REQ_NOW);
  assert property (disable iff (rst) past1 |-> slave_wr   == rin0[66]);
  assert property (disable iff (rst) past1 |-> slave_mask == rin0[59:56]);
  assert property (disable iff (rst) past1 |-> slave_addr == {rin0[55:34], 2'b00});
  assert property (disable iff (rst) past1 |-> slave_wdata== rin0[31:0]);

  // Response outputs mirror rin1 fields; rdone/wdone partition on wr
  assert property (disable iff (rst) past2 |-> rsp_seq  == rin1[33:32]);
  assert property (disable iff (rst) past2 |-> rsp_mask == rin1[59:56]);
  assert property (disable iff (rst) past2 |-> rsp_addr == {rin1[55:34], 2'b00});
  assert property (disable iff (rst) past2 |-> rsp_data == rin1[31:0]);
  assert property (disable iff (rst) past2 |-> rdone == (MY_RESP_NOW && !rin1[66]));
  assert property (disable iff (rst) past2 |-> wdone == (MY_RESP_NOW &&  rin1[66]));
  assert property (disable iff (rst) !(rdone && wdone));
  assert property (disable iff (rst) (rdone || wdone) |-> (past2 && MY_RESP_NOW));

  // Output routing correctness (4-way mux)
  // 1) Highest priority: emit response when MY_REQ_D1
  assert property (disable iff (rst) past2 && MY_REQ_D1
                   |-> rcn_out == {1'b1, 1'b0, rin1[66:32], slave_rdata});

  // 2) Else inject request when CAN_INJECT
  assert property (disable iff (rst) past2 && !MY_REQ_D1 && CAN_INJECT
                   |-> rcn_out == {1'b1, 1'b1, wr, my_id, mask, addr[23:2], seq, wdata});

  // 3) Else, if my response present, emit bubble (zero)
  assert property (disable iff (rst) past2 && !MY_REQ_D1 && !CAN_INJECT && MY_RESP_NOW
                   |-> rcn_out == 69'd0);

  // 4) Else, forward prior flit
  assert property (disable iff (rst) past2 && !MY_REQ_D1 && !CAN_INJECT && !MY_RESP_NOW
                   |-> rcn_out == rin1);

  // Content checks on injected request fields
  assert property (disable iff (rst) past2 && !MY_REQ_D1 && CAN_INJECT
                   |-> (rcn_out[68] && rcn_out[67] && rcn_out[66] == wr
                        && rcn_out[65:60] == my_id
                        && rcn_out[59:56] == mask
                        && rcn_out[55:34] == addr[23:2]
                        && rcn_out[33:32] == seq
                        && rcn_out[31:0]  == wdata));

  // Content checks on emitted response fields
  assert property (disable iff (rst) past2 && MY_REQ_D1
                   |-> (rcn_out[68] && !rcn_out[67]
                        && rcn_out[66:32] == rin1[66:32]
                        && rcn_out[31:0]  == slave_rdata));

  // Key coverage
  cover property (disable iff (rst) past2 && !MY_REQ_D1 && CAN_INJECT && (wr==1)
                  && rcn_out[68] && rcn_out[67] && rcn_out[66]);
  cover property (disable iff (rst) past2 && !MY_REQ_D1 && CAN_INJECT && (wr==0)
                  && rcn_out[68] && rcn_out[67] && !rcn_out[66]);
  cover property (disable iff (rst) past2 && MY_REQ_D1 && rcn_out[68] && !rcn_out[67]);
  cover property (disable iff (rst) past2 && !MY_REQ_D1 && !CAN_INJECT && MY_RESP_NOW && (rcn_out==69'd0));
  cover property (disable iff (rst) past2 && !MY_REQ_D1 && !CAN_INJECT && !MY_RESP_NOW && (rcn_out==rin1));
  cover property (disable iff (rst) past2 && (rin1[68] && !MY_RESP_NOW) && busy);
  cover property (disable iff (rst) rdone);
  cover property (disable iff (rst) wdone);

endmodule

// Bind into the DUT
bind rcn_master_slave rcn_master_slave_sva #(
  .MASTER_ID(MASTER_ID),
  .ADDR_MASK(ADDR_MASK),
  .ADDR_BASE(ADDR_BASE)
) rcn_master_slave_sva_i (
  .* // relies on matching port names
);