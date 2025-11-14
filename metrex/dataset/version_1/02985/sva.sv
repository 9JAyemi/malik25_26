// SVA for non_posted_pkt_slicer
// Bind this file to the DUT
// bind non_posted_pkt_slicer npps_sva npps_sva_i();

module npps_sva;

  // Implicitly bound into non_posted_pkt_slicer scope; can see internals
  default clocking cb @(posedge clk); endclocking
  // Most properties disabled during rst; explicit reset/transferstart checks provided separately
  default disable iff (rst_reg);

  // Mirror state encodings
  localparam [3:0] IDLE              = 4'h0;
  localparam [3:0] IDLE_WAIT         = 4'h1;
  localparam [3:0] START             = 4'h2;
  localparam [3:0] NORMAL            = 4'h3;
  localparam [3:0] CROSS             = 4'h4;
  localparam [3:0] LAST              = 4'h5;
  localparam [3:0] WAIT_FOR_ACK      = 4'h6;
  localparam [3:0] REGISTER_DMA_REG  = 4'h7;
  localparam [3:0] START_TX_DES_REQ  = 4'h8;

  // 1) Sanity/reset
  assert property (state inside {IDLE,IDLE_WAIT,START,NORMAL,CROSS,LAST,WAIT_FOR_ACK,REGISTER_DMA_REG,START_TX_DES_REQ});

  // When rst_reg or transferstart deasserted, FSM/output baseline
  assert property ((rst_reg || !transferstart) |-> (state==IDLE && !update_dma_reg && !go && !last_flag && !stay_2x));

  // 2) IDLE behavior/transitions
  assert property (state==IDLE |-> (!go && !last_flag && !update_dma_reg && !stay_2x));
  assert property (state==IDLE && rd_dma_start |=> state==IDLE_WAIT);
  assert property (state==IDLE && !rd_dma_start && rd_TX_des_start_one |=> state==START_TX_DES_REQ);
  assert property (state==IDLE && !rd_dma_start && !rd_TX_des_start_one |=> state==IDLE);

  // 3) IDLE_WAIT -> START
  assert property (state==IDLE_WAIT |-> !go);
  assert property (state==IDLE_WAIT |=> state==START);

  // 4) START outputs and next-state decode
  assert property (state==START |-> (!go && !update_dma_reg && !stay_2x));
  assert property (state==START && {four_kb_cross,less_than_rrs}==2'b00 |=> state==NORMAL);
  assert property (state==START && {four_kb_cross,less_than_rrs}==2'b01 |=> state==LAST);
  assert property (state==START && {four_kb_cross,less_than_rrs}==2'b10 |=> state==CROSS);
  assert property (state==START && {four_kb_cross,less_than_rrs}==2'b11 && (dmarxs_reg >  four_kb_xfer) |=> state==CROSS);
  assert property (state==START && {four_kb_cross,less_than_rrs}==2'b11 && (dmarxs_reg <= four_kb_xfer) |=> state==LAST);

  // 5) Emit states NORMAL/CROSS/LAST: 2-cycle pattern and go asserted
  // NORMAL
  assert property (state==NORMAL |-> go);
  assert property (state==NORMAL && !stay_2x |=> state==NORMAL && stay_2x);
  assert property (state==NORMAL &&  stay_2x |=> state==WAIT_FOR_ACK && !stay_2x);
  // CROSS
  assert property (state==CROSS |-> go);
  assert property (state==CROSS && !stay_2x |=> state==CROSS && stay_2x);
  assert property (state==CROSS &&  stay_2x |=> state==WAIT_FOR_ACK && !stay_2x);
  // LAST (also asserts last_flag on exit)
  assert property (state==LAST |-> go);
  assert property (state==LAST && !stay_2x |=> state==LAST && stay_2x);
  assert property (state==LAST &&  stay_2x |=> state==WAIT_FOR_ACK && last_flag && !stay_2x);

  // 6) Descriptor request: 2-cycle pattern, go asserted, last_flag set when leaving
  assert property (state==START_TX_DES_REQ |-> go);
  assert property (state==START_TX_DES_REQ && !stay_2x |=> state==START_TX_DES_REQ && stay_2x);
  assert property (state==START_TX_DES_REQ &&  stay_2x |=> state==WAIT_FOR_ACK && last_flag && !stay_2x);

  // 7) WAIT_FOR_ACK handshake
  assert property (state==WAIT_FOR_ACK && !ack |-> (go && !update_dma_reg) && $stable(state));
  assert property (state==WAIT_FOR_ACK &&  ack |-> (!go && update_dma_reg));
  assert property (state==WAIT_FOR_ACK &&  ack &&  last_flag |=> state==IDLE);
  assert property (state==WAIT_FOR_ACK &&  ack && !last_flag |=> state==REGISTER_DMA_REG);
  // Update only occurs in WAIT_FOR_ACK with ack, and is 1-cycle pulse
  assert property (update_dma_reg |-> (state==WAIT_FOR_ACK && ack));
  assert property (update_dma_reg |=> !update_dma_reg);

  // 8) REGISTER_DMA_REG one-cycle and no-go
  assert property (state==REGISTER_DMA_REG |-> !update_dma_reg && !go);
  assert property (state==REGISTER_DMA_REG |=> state==IDLE_WAIT);

  // 9) isDes behavior
  assert property (state==START_TX_DES_REQ |-> isDes);
  assert property ((state==NORMAL || state==CROSS || state==LAST) |-> !isDes);

  // 10) length programming (registered one cycle after state matches)
  assert property (rst_reg |-> length==10'd0);
  assert property (state==NORMAL           |=> length == read_req_size_bytes[11:2]);
  assert property (state==CROSS            |=> length == four_kb_xfer2[11:2]);
  assert property (state==LAST             |=> length == dmarxs_reg2[11:2]);
  assert property (state==START_TX_DES_REQ |=> length == 13'h0020[11:2]);

  // 11) Register update sequencing
  // Load on rd_dma_start (next cycle)
  assert property (rd_dma_start |=> (dmarad_reg  == $past(dmarad)  &&
                                     dmarxs_reg  == $past(dmarxs)  &&
                                     dmaras_reg  == $past(dmaras)  &&
                                     dmarad_reg2 == $past(dmarad)  &&
                                     dmarxs_reg2 == $past(dmarxs)  &&
                                     dmaras_reg2 == $past(dmaras)));
  // Update on update_dma_reg (next cycle uses previously computed *_new)
  assert property (update_dma_reg |=> (dmarad_reg  == $past(dmarad_new) &&
                                       dmarxs_reg  == $past(dmarxs_new) &&
                                       dmaras_reg  == $past(dmaras_new) &&
                                       dmarad_reg2 == $past(dmarad_new) &&
                                       dmarxs_reg2 == $past(dmarxs_new) &&
                                       dmaras_reg2 == $past(dmaras_new)));
  // Hold when no load/update/descriptor write
  assert property (!rd_dma_start && !update_dma_reg && !rd_TX_des_start_one |=> ($stable(dmarad_reg)  &&
                                                                                $stable(dmarxs_reg)  &&
                                                                                $stable(dmaras_reg)));
  // Reg2 only changes on start/update
  assert property (!rd_dma_start && !update_dma_reg |=> ($stable(dmarad_reg2) &&
                                                        $stable(dmarxs_reg2) &&
                                                        $stable(dmaras_reg2)));

  // 12) Combinational helpers correctness
  assert property (less_than_rrs == (dmarxs_reg <= read_req_size_bytes));
  assert property (dmaras_temp == (dmaras_reg + read_req_size_bytes));
  assert property (four_kb_cross == (dmaras_temp[12] != dmaras_reg2[12]));

  // 13) GO behavior summary
  assert property ((state==IDLE || state==START || state==IDLE_WAIT || state==REGISTER_DMA_REG) |-> !go);
  assert property ((state==NORMAL || state==CROSS || state==LAST || state==START_TX_DES_REQ || (state==WAIT_FOR_ACK && !ack)) |-> go);

  // 14) Functional covers (key scenarios)
  cover property (state==IDLE && rd_dma_start ##1 state==IDLE_WAIT ##1 state==START ##1 state==NORMAL ##1 state==WAIT_FOR_ACK ##1 !ack [*1:$] ##1 ack ##1 state==REGISTER_DMA_REG ##1 state==IDLE_WAIT);
  cover property (state==IDLE && rd_dma_start ##1 state==START && four_kb_cross && !less_than_rrs ##1 state==CROSS ##1 state==WAIT_FOR_ACK ##1 ack ##1 state==REGISTER_DMA_REG);
  cover property (state==IDLE && rd_dma_start ##1 state==START && !four_kb_cross && less_than_rrs ##1 state==LAST ##1 state==WAIT_FOR_ACK ##1 ack ##1 state==IDLE);
  cover property (state==IDLE && rd_TX_des_start_one ##1 state==START_TX_DES_REQ ##1 state==START_TX_DES_REQ && stay_2x ##1 state==WAIT_FOR_ACK && last_flag ##1 ack ##1 state==IDLE);

endmodule

bind non_posted_pkt_slicer npps_sva npps_sva_i();