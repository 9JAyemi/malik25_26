// SVA for arbiter_for_OUT_rep
module arbiter_for_OUT_rep_sva (
  input  logic        clk,
  input  logic        rst,
  // inputs
  input  logic        OUT_rep_rdy,
  input  logic        v_dc_rep,
  input  logic        v_mem_rep,
  input  logic [15:0] dc_rep_flit,
  input  logic [15:0] mem_rep_flit,
  input  logic [1:0]  dc_rep_ctrl,
  input  logic [1:0]  mem_rep_ctrl,
  // outputs (observed)
  input  logic        ack_OUT_rep,
  input  logic        ack_dc_rep,
  input  logic        ack_mem_rep,
  input  logic [1:0]  select,
  // internals (observed)
  input  logic [2:0]  state,
  input  logic        priority1,
  input  logic        update_priority
);

  // mirror DUT params
  localparam logic [2:0] ARB_IDLE = 3'b001;
  localparam logic [2:0] DC_UP    = 3'b010;
  localparam logic [2:0] MEM_UP   = 3'b100;
  localparam logic [4:0] NACK_CMD = 5'b10101;
  localparam logic [4:0] SCFLU_CMD= 5'b11100;

  // clocking
  default clocking cb @(posedge clk); endclocking

  // Reset behavior
  assert property (@(posedge clk) rst |=> state==ARB_IDLE);
  assert property (@(posedge clk) rst |=> priority1==1'b0);

  // State/outputs encodings
  assert property (@(posedge clk) state inside {ARB_IDLE,DC_UP,MEM_UP});
  assert property (@(posedge clk) select inside {2'b00,2'b01,2'b10});
  assert property (@(posedge clk) !(ack_dc_rep && ack_mem_rep));
  assert property (@(posedge clk) ack_OUT_rep == (ack_dc_rep || ack_mem_rep));

  // update_priority behavior (only when both valid in IDLE, and iff)
  assert property (@(posedge clk) disable iff (rst) update_priority <-> (state==ARB_IDLE && v_dc_rep && v_mem_rep));

  // priority1 toggling only when update_priority
  assert property (@(posedge clk) disable iff (rst) update_priority |=> priority1 != $past(priority1));
  assert property (@(posedge clk) disable iff (rst) !update_priority |=> priority1 == $past(priority1));

  // Idle transitions
  assert property (@(posedge clk) disable iff (rst) (state==ARB_IDLE && !v_dc_rep && !v_mem_rep) |=> state==ARB_IDLE);
  assert property (@(posedge clk) disable iff (rst) (state==ARB_IDLE && v_dc_rep && !v_mem_rep)  |=> state==DC_UP);
  assert property (@(posedge clk) disable iff (rst) (state==ARB_IDLE && !v_dc_rep && v_mem_rep)  |=> state==MEM_UP);
  assert property (@(posedge clk) disable iff (rst) (state==ARB_IDLE && v_dc_rep && v_mem_rep &&  priority1) |=> state==DC_UP);
  assert property (@(posedge clk) disable iff (rst) (state==ARB_IDLE && v_dc_rep && v_mem_rep && !priority1) |=> state==MEM_UP);

  // No acks/select in IDLE
  assert property (@(posedge clk) state==ARB_IDLE |-> (!ack_OUT_rep && !ack_dc_rep && !ack_mem_rep && select==2'b00));

  // DC uploading handshake
  assert property (@(posedge clk) disable iff (rst)
    (state==DC_UP && OUT_rep_rdy) |-> (ack_OUT_rep && ack_dc_rep && !ack_mem_rep && select==2'b01));
  assert property (@(posedge clk) disable iff (rst)
    (state==DC_UP && !OUT_rep_rdy) |-> (!ack_OUT_rep && !ack_dc_rep && select==2'b00));
  assert property (@(posedge clk) disable iff (rst)
    ack_dc_rep |-> (state==DC_UP && OUT_rep_rdy && select==2'b01));
  assert property (@(posedge clk) disable iff (rst)
    (select==2'b01) |-> (state==DC_UP && OUT_rep_rdy && ack_dc_rep && ack_OUT_rep));

  // MEM uploading handshake
  assert property (@(posedge clk) disable iff (rst)
    (state==MEM_UP && OUT_rep_rdy) |-> (ack_OUT_rep && ack_mem_rep && !ack_dc_rep && select==2'b10));
  assert property (@(posedge clk) disable iff (rst)
    (state==MEM_UP && !OUT_rep_rdy) |-> (!ack_OUT_rep && !ack_mem_rep && select==2'b00));
  assert property (@(posedge clk) disable iff (rst)
    ack_mem_rep |-> (state==MEM_UP && OUT_rep_rdy && select==2'b10));
  assert property (@(posedge clk) disable iff (rst)
    (select==2'b10) |-> (state==MEM_UP && OUT_rep_rdy && ack_mem_rep && ack_OUT_rep));

  // DC termination to IDLE when last/command seen
  assert property (@(posedge clk) disable iff (rst)
    (state==DC_UP && OUT_rep_rdy &&
     (dc_rep_ctrl==2'b11 || (dc_rep_ctrl==2'b01 && (dc_rep_flit[9:5]==SCFLU_CMD || dc_rep_flit[9:5]==NACK_CMD))))
    |=> state==ARB_IDLE);

  // DC stay when not last/command (even when ready)
  assert property (@(posedge clk) disable iff (rst)
    (state==DC_UP && OUT_rep_rdy &&
     !(dc_rep_ctrl==2'b11 || (dc_rep_ctrl==2'b01 && (dc_rep_flit[9:5]==SCFLU_CMD || dc_rep_flit[9:5]==NACK_CMD))))
    |=> state==DC_UP);

  // DC stay when not ready
  assert property (@(posedge clk) disable iff (rst)
    (state==DC_UP && !OUT_rep_rdy) |=> state==DC_UP);

  // MEM termination to IDLE when last/command seen
  assert property (@(posedge clk) disable iff (rst)
    (state==MEM_UP && OUT_rep_rdy &&
     (mem_rep_ctrl==2'b11 || (mem_rep_ctrl==2'b01 && (mem_rep_flit[9:5]==SCFLU_CMD || mem_rep_flit[9:5]==NACK_CMD))))
    |=> state==ARB_IDLE);

  // MEM stay when not last/command (even when ready)
  assert property (@(posedge clk) disable iff (rst)
    (state==MEM_UP && OUT_rep_rdy &&
     !(mem_rep_ctrl==2'b11 || (mem_rep_ctrl==2'b01 && (mem_rep_flit[9:5]==SCFLU_CMD || mem_rep_flit[9:5]==NACK_CMD))))
    |=> state==MEM_UP);

  // MEM stay when not ready
  assert property (@(posedge clk) disable iff (rst)
    (state==MEM_UP && !OUT_rep_rdy) |=> state==MEM_UP);

  // Illegal direct cross transitions blocked (redundant given above, but explicit)
  assert property (@(posedge clk) disable iff (rst) $past(state)==DC_UP  && state==MEM_UP  |-> 0);
  assert property (@(posedge clk) disable iff (rst) $past(state)==MEM_UP && state==DC_UP   |-> 0);

  // Coverage
  cover property (@(posedge clk) disable iff (rst)
    state==ARB_IDLE && v_dc_rep && v_mem_rep &&  priority1 ##1 state==DC_UP);
  cover property (@(posedge clk) disable iff (rst)
    state==ARB_IDLE && v_dc_rep && v_mem_rep && !priority1 ##1 state==MEM_UP);

  cover property (@(posedge clk) disable iff (rst)
    state==DC_UP ##[1:5] OUT_rep_rdy && ack_OUT_rep && ack_dc_rep);
  cover property (@(posedge clk) disable iff (rst)
    state==MEM_UP ##[1:5] OUT_rep_rdy && ack_OUT_rep && ack_mem_rep);

  cover property (@(posedge clk) disable iff (rst)
    state==DC_UP ##1 OUT_rep_rdy && dc_rep_ctrl==2'b11 ##1 state==ARB_IDLE);
  cover property (@(posedge clk) disable iff (rst)
    state==MEM_UP ##1 OUT_rep_rdy && mem_rep_ctrl==2'b11 ##1 state==ARB_IDLE);

  cover property (@(posedge clk) disable iff (rst)
    state==DC_UP ##1 OUT_rep_rdy && dc_rep_ctrl==2'b01 && (dc_rep_flit[9:5]==SCFLU_CMD) ##1 state==ARB_IDLE);
  cover property (@(posedge clk) disable iff (rst)
    state==DC_UP ##1 OUT_rep_rdy && dc_rep_ctrl==2'b01 && (dc_rep_flit[9:5]==NACK_CMD)  ##1 state==ARB_IDLE);

  cover property (@(posedge clk) disable iff (rst)
    state==MEM_UP ##1 OUT_rep_rdy && mem_rep_ctrl==2'b01 && (mem_rep_flit[9:5]==SCFLU_CMD) ##1 state==ARB_IDLE);
  cover property (@(posedge clk) disable iff (rst)
    state==MEM_UP ##1 OUT_rep_rdy && mem_rep_ctrl==2'b01 && (mem_rep_flit[9:5]==NACK_CMD)  ##1 state==ARB_IDLE);

  cover property (@(posedge clk) disable iff (rst)
    state==DC_UP ##1 !OUT_rep_rdy [*2] ##1 OUT_rep_rdy && ack_dc_rep);
  cover property (@(posedge clk) disable iff (rst)
    state==MEM_UP ##1 !OUT_rep_rdy [*2] ##1 OUT_rep_rdy && ack_mem_rep);

  cover property (@(posedge clk) disable iff (rst)
    state==ARB_IDLE && v_dc_rep && v_mem_rep ##1 priority1 != $past(priority1));

endmodule

// Bind into DUT (example)
bind arbiter_for_OUT_rep arbiter_for_OUT_rep_sva sva (
  .clk(clk),
  .rst(rst),
  .OUT_rep_rdy(OUT_rep_rdy),
  .v_dc_rep(v_dc_rep),
  .v_mem_rep(v_mem_rep),
  .dc_rep_flit(dc_rep_flit),
  .mem_rep_flit(mem_rep_flit),
  .dc_rep_ctrl(dc_rep_ctrl),
  .mem_rep_ctrl(mem_rep_ctrl),
  .ack_OUT_rep(ack_OUT_rep),
  .ack_dc_rep(ack_dc_rep),
  .ack_mem_rep(ack_mem_rep),
  .select(select),
  .state(state),
  .priority1(priority1),
  .update_priority(update_priority)
);