// SVA for xcvr_ctrl
// Bind this module to the DUT: bind xcvr_ctrl xcvr_ctrl_sva u_xcvr_ctrl_sva();

module xcvr_ctrl_sva;

  // Re-declare state encodings for readability
  localparam [3:0]
    STATE_IDLE          = 4'd0,
    STATE_LOAD_PMA_1    = 4'd1,
    STATE_LOAD_PMA_2    = 4'd2,
    STATE_INIT_ADAPT_1  = 4'd3,
    STATE_INIT_ADAPT_2  = 4'd4,
    STATE_INIT_ADAPT_3  = 4'd5,
    STATE_INIT_ADAPT_4  = 4'd6,
    STATE_CONT_ADAPT_1  = 4'd7,
    STATE_CONT_ADAPT_2  = 4'd8,
    STATE_CONT_ADAPT_3  = 4'd9,
    STATE_CONT_ADAPT_4  = 4'd10,
    STATE_DONE          = 4'd11;

  default clocking cb @(posedge reconfig_clk); endclocking
  default disable iff (reconfig_rst);

  // Short aliases
  wire [3:0] st        = state_reg;
  wire       rw_busy   = xcvr_reconfig_read || xcvr_reconfig_write;

  // 1) Basic protocol safety
  assert property (!(xcvr_reconfig_read && xcvr_reconfig_write));

  // Hold read/write and addr/data stable while waitrequest is asserted
  assert property ( (rw_busy && xcvr_reconfig_waitrequest)
                    |-> ( (rw_busy && $stable(xcvr_reconfig_address) && $stable(xcvr_reconfig_writedata))
                          throughout (xcvr_reconfig_waitrequest)) );

  // Drop read/write after a non-stalled cycle
  assert property ( (rw_busy && !xcvr_reconfig_waitrequest) |=> (!xcvr_reconfig_read && !xcvr_reconfig_write) );

  // Allowed read/write targets only
  assert property ( xcvr_reconfig_read
                    |-> (xcvr_reconfig_address == 19'h40144 || xcvr_reconfig_address == 19'h207) );

  assert property ( xcvr_reconfig_write
                    |-> ( (xcvr_reconfig_address == 19'h40143 && xcvr_reconfig_writedata == 8'h80)
                       ||   (xcvr_reconfig_address == 19'h200   && (xcvr_reconfig_writedata == 8'hD2 || xcvr_reconfig_writedata == 8'hF6))
                       ||   (xcvr_reconfig_address == 19'h201   && (xcvr_reconfig_writedata == 8'h02 || xcvr_reconfig_writedata == 8'h01))
                       ||   (xcvr_reconfig_address == 19'h202   && (xcvr_reconfig_writedata == 8'h01 || xcvr_reconfig_writedata == 8'h03))
                       ||   (xcvr_reconfig_address == 19'h203   &&  xcvr_reconfig_writedata == 8'h96) ) );

  // 2) Read data capture correctness
  // read_data_valid is a 1-cycle pulse caused by a successful read handshake; data matches bus from previous cycle
  assert property ( read_data_valid_reg |-> $past(xcvr_reconfig_read && !xcvr_reconfig_waitrequest) );
  assert property ( read_data_valid_reg |-> (read_data_reg == $past(xcvr_reconfig_readdata)) );
  assert property ( read_data_valid_reg |=> !read_data_valid_reg );

  // 3) State machine invariants
  // State freezes while busy
  assert property ( rw_busy |=> state_reg == $past(state_reg) );

  // State freezes and delay_count decrements while delaying (and not busy)
  assert property ( (!rw_busy && delay_count_reg != 0) |=> (state_reg == $past(state_reg) && delay_count_reg == $past(delay_count_reg) - 1) );

  // Lock drop forces IDLE next cycle
  assert property ( !pll_locked_sync_3_reg |=> state_reg == STATE_IDLE );

  // On entering from IDLE with lock high, load delay and go to LOAD_PMA_1
  assert property ( $past(st) == STATE_IDLE && $past(pll_locked_sync_3_reg)
                    |-> (state_reg == STATE_LOAD_PMA_1 && delay_count_reg == 16'hFFFF) );

  // Allowed state transitions (excluding reset/lock-drop paths)
  assert property (
    pll_locked_sync_3_reg &&
    ( $past(st) != state_reg ) |->
      ( ($past(st) == STATE_IDLE)          -> (state_reg == STATE_LOAD_PMA_1) ) &&
      ( ($past(st) == STATE_LOAD_PMA_1)    -> (state_reg == STATE_LOAD_PMA_2) ) &&
      ( ($past(st) == STATE_LOAD_PMA_2)    -> (state_reg == STATE_LOAD_PMA_2 || state_reg == STATE_INIT_ADAPT_1) ) &&
      ( ($past(st) == STATE_INIT_ADAPT_1)  -> (state_reg == STATE_INIT_ADAPT_2) ) &&
      ( ($past(st) == STATE_INIT_ADAPT_2)  -> (state_reg == STATE_INIT_ADAPT_3) ) &&
      ( ($past(st) == STATE_INIT_ADAPT_3)  -> (state_reg == STATE_INIT_ADAPT_4) ) &&
      ( ($past(st) == STATE_INIT_ADAPT_4)  -> (state_reg == STATE_INIT_ADAPT_4 || state_reg == STATE_CONT_ADAPT_1) ) &&
      ( ($past(st) == STATE_CONT_ADAPT_1)  -> (state_reg == STATE_CONT_ADAPT_2) ) &&
      ( ($past(st) == STATE_CONT_ADAPT_2)  -> (state_reg == STATE_CONT_ADAPT_3) ) &&
      ( ($past(st) == STATE_CONT_ADAPT_3)  -> (state_reg == STATE_CONT_ADAPT_4) ) &&
      ( ($past(st) == STATE_CONT_ADAPT_4)  -> (state_reg == STATE_CONT_ADAPT_4 || state_reg == STATE_DONE) ) &&
      ( ($past(st) == STATE_DONE)          -> (state_reg == STATE_DONE || !pll_locked_sync_3_reg) )
  );

  // DONE must not issue bus ops
  assert property ( state_reg == STATE_DONE |-> (!xcvr_reconfig_read && !xcvr_reconfig_write) );

  // 4) Per-state operation checks at the action point (delay done and not busy)
  // LOAD_PMA_1 issues write 0x40143<-0x80 and advances to LOAD_PMA_2
  assert property ( st == STATE_LOAD_PMA_1 && delay_count_reg == 0 && !rw_busy
                    |=> (xcvr_reconfig_write && xcvr_reconfig_address == 19'h40143 && xcvr_reconfig_writedata == 8'h80
                         && state_reg == STATE_LOAD_PMA_2) );

  // LOAD_PMA_2 branches
  assert property ( st == STATE_LOAD_PMA_2 && read_data_valid_reg && read_data_reg[0]
                    |=> (xcvr_reconfig_write && xcvr_reconfig_address == 19'h200 && xcvr_reconfig_writedata == 8'hD2
                         && state_reg == STATE_INIT_ADAPT_1) );
  assert property ( st == STATE_LOAD_PMA_2 && !(read_data_valid_reg && read_data_reg[0])
                    |=> (xcvr_reconfig_read && xcvr_reconfig_address == 19'h40144
                         && state_reg == STATE_LOAD_PMA_2) );

  // INIT_ADAPT_1..3 straight writes
  assert property ( st == STATE_INIT_ADAPT_1 |=> (xcvr_reconfig_write && xcvr_reconfig_address == 19'h201 && xcvr_reconfig_writedata == 8'h02
                                                  && state_reg == STATE_INIT_ADAPT_2) );
  assert property ( st == STATE_INIT_ADAPT_2 |=> (xcvr_reconfig_write && xcvr_reconfig_address == 19'h202 && xcvr_reconfig_writedata == 8'h01
                                                  && state_reg == STATE_INIT_ADAPT_3) );
  assert property ( st == STATE_INIT_ADAPT_3 |=> (xcvr_reconfig_write && xcvr_reconfig_address == 19'h203 && xcvr_reconfig_writedata == 8'h96
                                                  && state_reg == STATE_INIT_ADAPT_4) );

  // INIT_ADAPT_4 branches on 0x207==0x80
  assert property ( st == STATE_INIT_ADAPT_4 && read_data_valid_reg && read_data_reg == 8'h80
                    |=> (xcvr_reconfig_write && xcvr_reconfig_address == 19'h200 && xcvr_reconfig_writedata == 8'hF6
                         && state_reg == STATE_CONT_ADAPT_1) );
  assert property ( st == STATE_INIT_ADAPT_4 && !(read_data_valid_reg && read_data_reg == 8'h80)
                    |=> (xcvr_reconfig_read && xcvr_reconfig_address == 19'h207
                         && state_reg == STATE_INIT_ADAPT_4) );

  // CONT_ADAPT_1..3 straight writes
  assert property ( st == STATE_CONT_ADAPT_1 |=> (xcvr_reconfig_write && xcvr_reconfig_address == 19'h201 && xcvr_reconfig_writedata == 8'h01
                                                  && state_reg == STATE_CONT_ADAPT_2) );
  assert property ( st == STATE_CONT_ADAPT_2 |=> (xcvr_reconfig_write && xcvr_reconfig_address == 19'h202 && xcvr_reconfig_writedata == 8'h03
                                                  && state_reg == STATE_CONT_ADAPT_3) );
  assert property ( st == STATE_CONT_ADAPT_3 |=> (xcvr_reconfig_write && xcvr_reconfig_address == 19'h203 && xcvr_reconfig_writedata == 8'h96
                                                  && state_reg == STATE_CONT_ADAPT_4) );

  // CONT_ADAPT_4 branches to DONE on 0x207==0x80, else re-read
  assert property ( st == STATE_CONT_ADAPT_4 && read_data_valid_reg && read_data_reg == 8'h80
                    |=> (state_reg == STATE_DONE && !xcvr_reconfig_read && !xcvr_reconfig_write) );
  assert property ( st == STATE_CONT_ADAPT_4 && !(read_data_valid_reg && read_data_reg == 8'h80)
                    |=> (xcvr_reconfig_read && xcvr_reconfig_address == 19'h207
                         && state_reg == STATE_CONT_ADAPT_4) );

  // 5) Reset post-conditions (synchronous)
  assert property ( $rose(reconfig_rst) |=> (state_reg == STATE_IDLE
                                            && !xcvr_reconfig_read && !xcvr_reconfig_write
                                            && !read_data_valid_reg
                                            && delay_count_reg == 0) );

  // 6) Coverage
  // Full flow to DONE after lock
  cover property ( $rose(pll_locked_sync_3_reg) ##[1:$] state_reg == STATE_DONE );

  // Exercise waitrequest during a write
  cover property ( xcvr_reconfig_write && xcvr_reconfig_waitrequest
                   ##1 xcvr_reconfig_write && xcvr_reconfig_waitrequest
                   ##1 xcvr_reconfig_write && !xcvr_reconfig_waitrequest );

  // LOAD_PMA_2 branch where condition met
  cover property ( state_reg == STATE_LOAD_PMA_2 && read_data_valid_reg && read_data_reg[0]
                   ##1 xcvr_reconfig_write && xcvr_reconfig_address == 19'h200 && xcvr_reconfig_writedata == 8'hD2 );

  // INIT_ADAPT_4 branch success path
  cover property ( state_reg == STATE_INIT_ADAPT_4 && read_data_valid_reg && read_data_reg == 8'h80
                   ##1 xcvr_reconfig_write && xcvr_reconfig_address == 19'h200 && xcvr_reconfig_writedata == 8'hF6 );

  // CONT_ADAPT_4 loop and success to DONE
  cover property ( state_reg == STATE_CONT_ADAPT_4 && !(read_data_valid_reg && read_data_reg == 8'h80)
                   ##1 xcvr_reconfig_read && xcvr_reconfig_address == 19'h207
                   ##[1:$] (state_reg == STATE_CONT_ADAPT_4 && read_data_valid_reg && read_data_reg == 8'h80)
                   ##1 state_reg == STATE_DONE );

  // Lock drop recovery
  cover property ( state_reg != STATE_IDLE && !pll_locked_sync_3_reg ##1 state_reg == STATE_IDLE );

endmodule