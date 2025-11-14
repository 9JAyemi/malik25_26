// SVA for blockram_spool
module blockram_spool_sva (
  input  logic         clk_i,
  input  logic         areset_i,
  input  logic [15:0]  address_o,
  input  logic [7:0]   data_o,
  input  logic [7:0]   q_i,
  input  logic         wren_o,
  input  logic [3:0]   A_i,
  input  logic [7:0]   D_i,
  input  logic [7:0]   D_o,
  input  logic         rd_i,
  input  logic         wr_i,
  input  logic [15:0]  A,
  input  logic         cpu_rd, cpu_wr, cpu_abort,
  input  logic         fsm_rd, fsm_wr, fsm_abort,
  input  logic [3:0]   state,
  input  logic [7:0]   rd_buffer,
  input  logic         rd_sig, wr_sig, abort_sig,
  input  logic         read_trigger, write_trigger
);
  localparam IDLE        = 4'd0;
  localparam PRE_READ    = 4'd1;
  localparam READ_READY  = 4'd2;
  localparam READ_CAPTURE= 4'd4;
  localparam WAIT_READ   = 4'd5;
  localparam WRITE_WAIT  = 4'd6;
  localparam WRITE_NEXT  = 4'd7;

  default clocking cb @ (posedge clk_i); endclocking
  default disable iff (areset_i);

  // Basic consistency
  a_no_x_state:        assert property (!$isunknown(state));
  a_state_valid:       assert property (state inside {IDLE,PRE_READ,READ_READY,READ_CAPTURE,WAIT_READ,WRITE_WAIT,WRITE_NEXT});
  a_sig_defs_rd:       assert property (rd_sig    == (cpu_rd    ^ fsm_rd));
  a_sig_defs_wr:       assert property (wr_sig    == (cpu_wr    ^ fsm_wr));
  a_sig_defs_abort:    assert property (abort_sig == (cpu_abort ^ fsm_abort));
  a_trig_def_r:        assert property (read_trigger  == ((A_i==4'd8) && rd_i));
  a_trig_def_w:        assert property (write_trigger == ((A_i==4'd8) && wr_i));

  // Reset observable values
  a_reset_vals:        assert property (@cb areset_i |=> state==IDLE && address_o==16'd0 && data_o==8'd0 && wren_o==1'b0 && fsm_rd==0 && fsm_wr==0 && fsm_abort==0 && D_o==8'd0);

  // IDLE behavior and priorities
  a_idle_hold:         assert property (state==IDLE && !(rd_sig||wr_sig) |=> state==IDLE);
  a_idle_rd:           assert property (state==IDLE && rd_sig && !wr_sig |=> state==PRE_READ && (fsm_rd != $past(fsm_rd)));
  a_idle_wr:           assert property (state==IDLE && wr_sig && !rd_sig |=> state==WRITE_WAIT && (fsm_wr != $past(fsm_wr)));
  a_idle_both_prio:    assert property (state==IDLE && rd_sig && wr_sig |=> state==PRE_READ && (fsm_rd != $past(fsm_rd)) && (fsm_wr == $past(fsm_wr)));
  a_idle_addr_eq_A:    assert property (state==IDLE |-> address_o == A);

  // Read path
  a_pre_to_ready:      assert property (state==PRE_READ |=> state==READ_READY);
  a_ready_incr:        assert property (state==READ_READY |-> address_o == $past(address_o)+16'd1);
  a_ready_to_capture:  assert property (state==READ_READY |=> state==READ_CAPTURE);
  a_capture_grab_q:    assert property (state==READ_CAPTURE |-> rd_buffer == q_i);
  a_capture_to_wait:   assert property (state==READ_CAPTURE |=> state==WAIT_READ);
  a_wait_abort:        assert property (state==WAIT_READ && abort_sig |=> state==IDLE && (fsm_abort != $past(fsm_abort)));
  a_wait_read_again:   assert property (state==WAIT_READ && !abort_sig && read_trigger |=> state==READ_READY);
  a_wait_hold:         assert property (state==WAIT_READ && !abort_sig && !read_trigger |=> state==WAIT_READ);

  // Write path
  a_ww_abort:          assert property (state==WRITE_WAIT && abort_sig |=> state==IDLE && (fsm_abort != $past(fsm_abort)));
  a_ww_fire_wren:      assert property (state==WRITE_WAIT && !abort_sig && write_trigger |-> wren_o);
  a_ww_to_wnext:       assert property (state==WRITE_WAIT && !abort_sig && write_trigger |=> state==WRITE_NEXT && !wren_o);
  a_ww_hold:           assert property (state==WRITE_WAIT && !abort_sig && !write_trigger |=> state==WRITE_WAIT);
  a_wn_incr_addr:      assert property (state==WRITE_NEXT |-> address_o == $past(address_o)+16'd1);
  a_wn_to_ww:          assert property (state==WRITE_NEXT |=> state==WRITE_WAIT);

  // WREN pulse properties
  a_wren_only_from_ww: assert property (wren_o |-> $past(state==WRITE_WAIT && write_trigger) && state==WRITE_NEXT);
  a_wren_one_cycle:    assert property (!(wren_o && $past(wren_o)));
  a_wren_datao_matches:assert property (wren_o |-> data_o == D_i);

  // CPU visible register behavior
  a_A_lo_write:        assert property (wr_i && A_i==4'd0 |-> A[7:0]  == D_i);
  a_A_hi_write:        assert property (wr_i && A_i==4'd1 |-> A[15:8] == D_i);
  a_A_lo_read:         assert property (rd_i && A_i==4'd0 |-> D_o == A[7:0]);
  a_A_hi_read:         assert property (rd_i && A_i==4'd1 |-> D_o == A[15:8]);
  a_rd_buf_read:       assert property (rd_i && A_i==4'd8 |-> D_o == rd_buffer);
  a_ctrl_read_zero:    assert property (rd_i && A_i==4'd15 |-> D_o == 8'h00);

  // CPU control toggle correctness
  a_cpu_rd_toggle_src:    assert property ($changed(cpu_rd)    |-> wr_i && A_i==4'd15 && D_i[0] && !rd_sig);
  a_cpu_wr_toggle_src:    assert property ($changed(cpu_wr)    |-> wr_i && A_i==4'd15 && D_i[1] && !wr_sig);
  a_cpu_abt_toggle_src:   assert property ($changed(cpu_abort) |-> wr_i && A_i==4'd15 && D_i[7] && !abort_sig);

  // Simple X checks on key outputs
  a_no_x_wren:         assert property (!$isunknown(wren_o));
  a_no_x_addr:         assert property (!$isunknown(address_o));
  a_no_x_datao:        assert property (!$isunknown(data_o));

  // Coverage
  c_states:            cover property (state inside {IDLE,PRE_READ,READ_READY,READ_CAPTURE,WAIT_READ,WRITE_WAIT,WRITE_NEXT});
  c_rd_flow:           cover property (state==IDLE && rd_sig ##1 state==PRE_READ ##1 state==READ_READY ##1 state==READ_CAPTURE ##1 state==WAIT_READ ##1 read_trigger ##1 state==READ_READY);
  c_wr_two_pulses:     cover property (state==IDLE && wr_sig ##1 state==WRITE_WAIT && write_trigger ##1 state==WRITE_NEXT ##1 state==WRITE_WAIT && write_trigger ##1 state==WRITE_NEXT);
  c_abort_read:        cover property (state==IDLE && rd_sig ##1 state==PRE_READ ##1 state==READ_READY ##1 state==READ_CAPTURE ##1 state==WAIT_READ && abort_sig ##1 state==IDLE);
  c_abort_write:       cover property (state==IDLE && wr_sig ##1 state==WRITE_WAIT && abort_sig ##1 state==IDLE);
  c_rd_vs_wr_prio:     cover property (state==IDLE && rd_sig && wr_sig ##1 state==PRE_READ);
  c_cpu_ctrl_toggles:  cover property (wr_i && A_i==4'd15 && (D_i[0]||D_i[1]||D_i[7]) && ($changed(cpu_rd)||$changed(cpu_wr)||$changed(cpu_abort)));
endmodule

// Bind into DUT
bind blockram_spool blockram_spool_sva sva (
  .clk_i(clk_i),
  .areset_i(areset_i),
  .address_o(address_o),
  .data_o(data_o),
  .q_i(q_i),
  .wren_o(wren_o),
  .A_i(A_i),
  .D_i(D_i),
  .D_o(D_o),
  .rd_i(rd_i),
  .wr_i(wr_i),
  .A(A),
  .cpu_rd(cpu_rd),
  .cpu_wr(cpu_wr),
  .cpu_abort(cpu_abort),
  .fsm_rd(fsm_rd),
  .fsm_wr(fsm_wr),
  .fsm_abort(fsm_abort),
  .state(state),
  .rd_buffer(rd_buffer),
  .rd_sig(rd_sig),
  .wr_sig(wr_sig),
  .abort_sig(abort_sig),
  .read_trigger(read_trigger),
  .write_trigger(write_trigger)
);