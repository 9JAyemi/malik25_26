// SVA for DRAMReader
// Concise checks for protocol, state/counter behavior, AXI handshake, and coverage.

module DRAMReader_sva (
  input logic         ACLK,
  input logic         ARESETN,

  input logic [31:0]  M_AXI_ARADDR,
  input logic         M_AXI_ARREADY,
  input logic         M_AXI_ARVALID,
  input logic  [3:0]  M_AXI_ARLEN,
  input logic  [1:0]  M_AXI_ARSIZE,
  input logic  [1:0]  M_AXI_ARBURST,

  input logic [63:0]  M_AXI_RDATA,
  input logic         M_AXI_RREADY,
  input logic  [1:0]  M_AXI_RRESP,
  input logic         M_AXI_RVALID,
  input logic         M_AXI_RLAST,

  input logic         CONFIG_VALID,
  input logic         CONFIG_READY,
  input logic [31:0]  CONFIG_START_ADDR,
  input logic [31:0]  CONFIG_NBYTES,

  input logic         DATA_READY_DOWNSTREAM,
  input logic         DATA_VALID,
  input logic [63:0]  DATA,

  // internal DUT state
  input logic [31:0]  a_count,
  input logic [31:0]  b_count,
  input logic         a_state,
  input logic         r_state
);

  default clocking @(posedge ACLK); endclocking
  default disable iff (!ARESETN)

  // Reset values
  assert property (!ARESETN |-> !M_AXI_ARVALID && !M_AXI_RREADY);

  // Constant AXI parameters
  assert property (M_AXI_ARLEN   == 4'hF);
  assert property (M_AXI_ARSIZE  == 2'b11);
  assert property (M_AXI_ARBURST == 2'b01);

  // Config protocol (environment)
  assert property (CONFIG_VALID |-> CONFIG_READY);
  assert property ((CONFIG_VALID && CONFIG_READY) |-> (CONFIG_START_ADDR[6:0]==0));
  assert property ((CONFIG_VALID && CONFIG_READY) |-> (CONFIG_NBYTES[6:0]==0 && CONFIG_NBYTES >= 32'd128));

  // Config acceptance effects next cycle
  assert property ((CONFIG_VALID && CONFIG_READY)
                   |=> (a_state && r_state) && // both RWAIT (1)
                       (a_count == CONFIG_NBYTES[31:7]) &&
                       (b_count == {CONFIG_NBYTES[31:7],7'b0}));

  // CONFIG_READY reflects both FSMs idle
  assert property (CONFIG_READY == (~a_state & ~r_state));

  // Address channel behavior
  assert property (M_AXI_ARVALID == a_state); // ARVALID iff a_state==RWAIT
  assert property (M_AXI_ARVALID && !M_AXI_ARREADY |-> $stable(M_AXI_ARADDR));
  assert property (M_AXI_ARVALID |-> (M_AXI_ARADDR[6:0]==0)); // 128B aligned

  // ARADDR sequencing
  property p_araddr_inc;
    (M_AXI_ARVALID && M_AXI_ARREADY) |=> (M_AXI_ARADDR == $past(M_AXI_ARADDR) + 32'd128);
  endproperty
  assert property (p_araddr_inc);

  // First AR after config uses start address
  logic awaiting_first_ar;
  always_ff @(posedge ACLK or negedge ARESETN) begin
    if (!ARESETN) awaiting_first_ar <= 1'b0;
    else if (CONFIG_VALID && CONFIG_READY) awaiting_first_ar <= 1'b1;
    else if (M_AXI_ARVALID && M_AXI_ARREADY) awaiting_first_ar <= 1'b0;
  end
  assert property (awaiting_first_ar && M_AXI_ARVALID && M_AXI_ARREADY |-> (M_AXI_ARADDR == CONFIG_START_ADDR));

  // a_count / a_state on AR handshake
  assert property (a_state && M_AXI_ARVALID && M_AXI_ARREADY |=> a_count == $past(a_count) - 1);
  assert property (a_state && M_AXI_ARVALID && M_AXI_ARREADY && $past(a_count)==32'd1 |=> !a_state);
  assert property (a_state && M_AXI_ARVALID && M_AXI_ARREADY && $past(a_count)>32'd1  |=> a_state);

  // R channel: master ready, data valid, data mapping
  assert property (M_AXI_RREADY == (r_state && DATA_READY_DOWNSTREAM));
  assert property (DATA_VALID == (M_AXI_RVALID && r_state));
  assert property (DATA == M_AXI_RDATA);

  // R channel: hold while not ready (slave behavior)
  assert property (M_AXI_RVALID && !M_AXI_RREADY |-> $stable({M_AXI_RDATA,M_AXI_RRESP,M_AXI_RLAST}));

  // RRESP OKAY on accepted beats
  assert property (M_AXI_RVALID && M_AXI_RREADY |-> M_AXI_RRESP == 2'b00);

  // b_count / r_state on R handshake
  assert property (r_state && M_AXI_RVALID && M_AXI_RREADY |=> b_count == $past(b_count) - 32'd8);
  assert property (r_state && M_AXI_RVALID && M_AXI_RREADY && $past(b_count)==32'd8 |=> !r_state);
  assert property (r_state && M_AXI_RVALID && M_AXI_RREADY && $past(b_count)>32'd8  |=> r_state);

  // Track outstanding beats and enforce RLAST position
  logic [31:0] beats_out;
  always_ff @(posedge ACLK or negedge ARESETN) begin
    if (!ARESETN) beats_out <= 32'd0;
    else begin
      if (CONFIG_VALID && CONFIG_READY) beats_out <= 32'd0;
      if (M_AXI_ARVALID && M_AXI_ARREADY) beats_out <= beats_out + 32'd16;
      if (M_AXI_RVALID && M_AXI_RREADY)   beats_out <= beats_out - 32'd1;
    end
  end

  // No R data unless something outstanding; no underflow
  assert property (beats_out==0 |-> !M_AXI_RVALID);
  assert property (M_AXI_RVALID && M_AXI_RREADY |-> beats_out > 0);

  // RLAST exactly on last beat of each 16-beat burst
  assert property (M_AXI_RVALID && M_AXI_RREADY |-> M_AXI_RLAST == (beats_out[3:0]==4'd1));

  // Cross-channel consistency: total beats equals 16 per AR
  sequence s_1cfg_to_done;
    (CONFIG_VALID && CONFIG_READY), ##1
    (1, beats_out==0) ##0;
  endsequence
  // cover: a multi-burst transaction completes
  cover property (CONFIG_VALID && CONFIG_READY ##1 (M_AXI_ARVALID && M_AXI_ARREADY)[*2:$] ##[1:$] (M_AXI_RVALID && M_AXI_RREADY && M_AXI_RLAST));

  // cover: AR backpressure then accept
  cover property (M_AXI_ARVALID && !M_AXI_ARREADY ##[1:$] M_AXI_ARVALID && M_AXI_ARREADY);

  // cover: R backpressure then accept
  cover property (M_AXI_RVALID && !M_AXI_RREADY ##[1:$] M_AXI_RVALID && M_AXI_RREADY && M_AXI_RLAST);

endmodule

// Bind into DUT
bind DRAMReader DRAMReader_sva u_dramreader_sva (
  .ACLK(ACLK),
  .ARESETN(ARESETN),

  .M_AXI_ARADDR(M_AXI_ARADDR),
  .M_AXI_ARREADY(M_AXI_ARREADY),
  .M_AXI_ARVALID(M_AXI_ARVALID),
  .M_AXI_ARLEN(M_AXI_ARLEN),
  .M_AXI_ARSIZE(M_AXI_ARSIZE),
  .M_AXI_ARBURST(M_AXI_ARBURST),

  .M_AXI_RDATA(M_AXI_RDATA),
  .M_AXI_RREADY(M_AXI_RREADY),
  .M_AXI_RRESP(M_AXI_RRESP),
  .M_AXI_RVALID(M_AXI_RVALID),
  .M_AXI_RLAST(M_AXI_RLAST),

  .CONFIG_VALID(CONFIG_VALID),
  .CONFIG_READY(CONFIG_READY),
  .CONFIG_START_ADDR(CONFIG_START_ADDR),
  .CONFIG_NBYTES(CONFIG_NBYTES),

  .DATA_READY_DOWNSTREAM(DATA_READY_DOWNSTREAM),
  .DATA_VALID(DATA_VALID),
  .DATA(DATA),

  .a_count(a_count),
  .b_count(b_count),
  .a_state(a_state),
  .r_state(r_state)
);