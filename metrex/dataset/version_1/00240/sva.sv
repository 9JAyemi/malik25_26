// SVA for eb_fifo_ctrl
// Bindable module that verifies protocol, counters, pointers, and combinational outputs.
// Minimal but high-quality checks with targeted coverage.

module eb_fifo_ctrl_sva_bind #(
  parameter int DEPTHMO     = 15,
  parameter int DEPTHLOG2MO = 3
) ();

  // Bound into eb_fifo_ctrl scope, so we can directly see DUT signals
  // clk, reset_n, t_0_req, t_0_ack, i_0_req, i_0_ack, wen, ren, wr_ptr, rd_ptr
  // internal: status_cnt, q_rd_ptr

  localparam int DEPTHP1 = DEPTHMO + 1;

  // convenient aliases
  let push = (t_0_req && t_0_ack);
  let pop  = (i_0_req && i_0_ack);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!reset_n)

  // Reset values
  a_reset_vals: assert property (!reset_n |-> (wr_ptr==0 && q_rd_ptr==0 && status_cnt==0 && i_0_req==0));

  // Simple combinational relationships
  a_t0ack_full: assert property (t_0_ack == (status_cnt != DEPTHMO));
  a_wen_def:    assert property (wen == (t_0_req && t_0_ack));
  a_ren_const:  assert property (ren == 1'b1);

  // Counter range and safety
  a_cnt_range:       assert property (status_cnt <= DEPTHMO);
  a_no_overflow:     assert property ((status_cnt == DEPTHMO) |-> !wen);
  a_no_underflow:    assert property (pop |-> (status_cnt > 0) || push);

  // Status counter next-state function
  a_cnt_inc:  assert property (push && !pop |=> status_cnt == $past(status_cnt)+1);
  a_cnt_dec:  assert property (pop  && !push |=> status_cnt == $past(status_cnt)-1);
  a_cnt_hold1:assert property (push &&  pop  |=> status_cnt == $past(status_cnt));
  a_cnt_hold0:assert property (!(push||pop) |=> status_cnt == $past(status_cnt));

  // i_0_req next-state logic (mirrors RTL branches)
  a_i0_req_empty: assert property ((status_cnt==0 && !push) |=> i_0_req==0);
  a_i0_req_last:  assert property ((pop && !push && status_cnt==1) |=> i_0_req==0);
  a_i0_req_else:  assert property (!((status_cnt==0 && !push) || (pop && !push && status_cnt==1)) |=> i_0_req==1);

  // wr_ptr update and hold
  a_wrptr_hold: assert property (!push |=> wr_ptr == $past(wr_ptr));
  a_wrptr_next: assert property ( push |=> wr_ptr == (($past(wr_ptr)==DEPTHMO)? '0 : $past(wr_ptr)+1));

  // q_rd_ptr update and hold (matches RTL's guarded wrap)
  a_qrdptr_hold: assert property (!pop |=> q_rd_ptr == $past(q_rd_ptr));
  a_qrdptr_next: assert property ( pop |=> q_rd_ptr == ((($past(q_rd_ptr)==DEPTHMO) && ($past(status_cnt)!=0)) ? '0 : ($past(q_rd_ptr)+1)));

  // rd_ptr combinational definition must mirror q_rd_ptr/handshake
  a_rdptr_comb: assert property (rd_ptr == (pop ? (((q_rd_ptr==DEPTHMO)&&(status_cnt!=0)) ? '0 : (q_rd_ptr+1)) : q_rd_ptr));

  // Pointer/count coherence: occupancy equals modular distance wr_ptr - q_rd_ptr
  function automatic int unsigned dist_mod(input logic [DEPTHLOG2MO:0] w, input logic [DEPTHLOG2MO:0] r);
    return (w>=r) ? (w-r) : (w + DEPTHP1 - r);
  endfunction
  a_cnt_ptr_consistent: assert property (dist_mod(wr_ptr, q_rd_ptr) == status_cnt);

  // Coverage
  c_empty:      cover property (status_cnt==0);
  c_full:       cover property (status_cnt==DEPTHMO);
  c_push_only:  cover property (push && !pop);
  c_pop_only:   cover property (pop && !push);
  c_both:       cover property (push && pop);
  c_stall:      cover property (!(push||pop));
  c_wr_wrap:    cover property ( (wr_ptr==DEPTHMO) ##1 push |=> wr_ptr==0 );
  c_rd_wrap:    cover property ( (q_rd_ptr==DEPTHMO && status_cnt!=0) ##1 pop |=> q_rd_ptr==0 );
  c_full_bp:    cover property (status_cnt==DEPTHMO && t_0_req && !t_0_ack && !wen);

endmodule

// Bind into the DUT (example; keep in your testbench or a bind file)
// bind eb_fifo_ctrl eb_fifo_ctrl_sva_bind #(.DEPTHMO(DEPTHMO), .DEPTHLOG2MO(DEPTHLOG2MO)) i_eb_fifo_ctrl_sva_bind();