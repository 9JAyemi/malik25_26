// SVA for wishbone_buf
// Bind this file to the DUT: bind wishbone_buf wishbone_buf_sva u_wishbone_buf_sva();

module wishbone_buf_sva (wishbone_buf dut);

  default clocking cb @(posedge dut.i_clk); endclocking

  bit f_past_valid;
  always_ff @(posedge dut.i_clk) f_past_valid <= 1'b1;

  // Helpers (purely combinational mirrors of DUT intent, evaluated on $past when needed)
  function automatic bit past_inc_cond;
    past_inc_cond = $past(dut.in_wreq) && !$past(dut.busy_reading_r) &&
                    ( ($past(dut.wbuf_used_r)==2'd1) ||
                      ($past(dut.wbuf_used_r)==2'd0 && !$past(dut.i_accepted)) );
  endfunction

  function automatic bit past_dec_cond;
    past_dec_cond = $past(dut.o_valid) && $past(dut.i_accepted) && ($past(dut.wbuf_used_r)!=2'd0);
  endfunction

  // Basic invariants
  assert property (f_past_valid |-> dut.wbuf_used_r <= 2);

  // Pointer relation vs. occupancy
  assert property (f_past_valid && dut.wbuf_used_r==0 |-> (dut.wbuf_rp_r == dut.wbuf_wp_r));
  assert property (f_past_valid && dut.wbuf_used_r==1 |-> (dut.wbuf_rp_r != dut.wbuf_wp_r));
  assert property (f_past_valid && dut.wbuf_used_r==2 |-> (dut.wbuf_rp_r == dut.wbuf_wp_r));

  // Exact occupancy update equation
  assert property (f_past_valid |-> dut.wbuf_used_r
      == $past(dut.wbuf_used_r)
         + (past_inc_cond ? 1 : 0)
         - (past_dec_cond ? 1 : 0));

  // Write pointer toggles iff a push happens (in_wreq && !o_ack)
  assert property (f_past_valid |-> (dut.in_wreq && !dut.o_ack) == (dut.wbuf_wp_r != $past(dut.wbuf_wp_r)));
  assert property (f_past_valid && !(dut.in_wreq && !dut.o_ack) |-> $stable(dut.wbuf_wp_r));

  // Read pointer toggles iff a pop happens (o_valid && i_accepted && wbuf_used_r!=0)
  assert property (f_past_valid |-> (dut.o_valid && dut.i_accepted && (dut.wbuf_used_r!=0)) == (dut.wbuf_rp_r != $past(dut.wbuf_rp_r)));
  assert property (f_past_valid && !(dut.o_valid && dut.i_accepted && (dut.wbuf_used_r!=0)) |-> $stable(dut.wbuf_rp_r));

  // While busy_reading, occupancy cannot increase
  assert property (f_past_valid && $past(dut.busy_reading_r) |-> dut.wbuf_used_r <= $past(dut.wbuf_used_r));

  // Captured data correctness on push (write-through captures i_* into the selected slot)
  assert property (f_past_valid && $past(dut.in_wreq && !dut.o_ack) && ($past(dut.wbuf_wp_r)==1'b0) |->
                   dut.wbuf_wdata_r0 == $past(dut.i_wdata) &&
                   dut.wbuf_addr_r0  == $past(dut.i_addr)  &&
                   dut.wbuf_be_r0    == $past(dut.i_be)    &&
                   dut.wbuf_write_r[0] == 1'b1);
  assert property (f_past_valid && $past(dut.in_wreq && !dut.o_ack) && ($past(dut.wbuf_wp_r)==1'b1) |->
                   dut.wbuf_wdata_r1 == $past(dut.i_wdata) &&
                   dut.wbuf_addr_r1  == $past(dut.i_addr)  &&
                   dut.wbuf_be_r1    == $past(dut.i_be)    &&
                   dut.wbuf_write_r[1] == 1'b1);

  // Output muxing correctness
  assert property (f_past_valid && (dut.wbuf_used_r!=0) |-> dut.o_wdata == (dut.wbuf_rp_r ? dut.wbuf_wdata_r1 : dut.wbuf_wdata_r0));
  assert property (f_past_valid && (dut.wbuf_used_r==0) |-> dut.o_wdata == dut.i_wdata);

  assert property (f_past_valid && (dut.wbuf_used_r!=0) |-> dut.o_addr == (dut.wbuf_rp_r ? dut.wbuf_addr_r1 : dut.wbuf_addr_r0));
  assert property (f_past_valid && (dut.wbuf_used_r==0) |-> dut.o_addr == dut.i_addr);

  assert property (f_past_valid && (dut.wbuf_used_r!=0) |-> dut.o_write == (dut.wbuf_rp_r ? dut.wbuf_write_r[1] : dut.wbuf_write_r[0]));
  assert property (f_past_valid && (dut.wbuf_used_r==0) |-> dut.o_write == dut.i_write);

  assert property (f_past_valid && (dut.wbuf_used_r!=0) |-> dut.o_be == (dut.wbuf_rp_r ? dut.wbuf_be_r1 : dut.wbuf_be_r0));
  assert property (f_past_valid && (dut.wbuf_used_r==0) |-> dut.o_be == (dut.i_write ? dut.i_be : 16'hffff));

  // o_valid gating and wait-for-read-data behavior
  assert property (f_past_valid |-> dut.o_valid == ((dut.wbuf_used_r!=0 || dut.i_req) && !dut.wait_rdata_valid_r));
  assert property (f_past_valid && (dut.o_valid && !dut.o_write && dut.i_accepted) |=> dut.wait_rdata_valid_r);
  assert property (f_past_valid && dut.i_rdata_valid |=> !dut.wait_rdata_valid_r);
  assert property (f_past_valid && dut.wait_rdata_valid_r |-> !dut.o_valid);

  // busy_reading behavior
  assert property (f_past_valid && (dut.o_valid && !dut.o_write) |=> dut.busy_reading_r);
  assert property (f_past_valid && dut.i_rdata_valid |=> !dut.busy_reading_r);

  // Read data path
  assert property (dut.o_rdata == dut.i_rdata);

  // ACK behavior
  // Immediate write ACK when write-through (buffer empty)
  assert property (f_past_valid && dut.in_wreq && (dut.wbuf_used_r==0) |-> dut.o_ack);

  // Buffered write ACK when owed and a buffered beat is accepted
  assert property (f_past_valid && dut.ack_owed_r && dut.o_valid && dut.i_accepted && (dut.wbuf_used_r!=0) |-> dut.o_ack);

  // Read ACK mirrors i_rdata_valid when not masked by write-ACK term
  assert property (f_past_valid && !dut.in_wreq &&
                   !(dut.ack_owed_r && dut.o_valid && dut.i_accepted && (dut.wbuf_used_r!=0))
                   |-> (dut.o_ack == dut.i_rdata_valid));

  // No spurious ACK
  assert property (f_past_valid &&
                   !dut.in_wreq && !dut.i_rdata_valid &&
                   !(dut.ack_owed_r && dut.o_valid && dut.i_accepted && (dut.wbuf_used_r!=0))
                   |-> !dut.o_ack);

  // Coverage
  cover property (f_past_valid && dut.wbuf_used_r==0 ##1 (dut.in_wreq && !dut.o_ack) ##1 dut.wbuf_used_r==1
                  ##1 (dut.in_wreq && !dut.o_ack) ##1 dut.wbuf_used_r==2);

  cover property (f_past_valid && dut.wbuf_used_r==2 ##1 (dut.o_valid && dut.i_accepted) ##1 dut.wbuf_used_r==1
                  ##1 (dut.o_valid && dut.i_accepted) ##1 dut.wbuf_used_r==0);

  cover property (f_past_valid && (dut.o_valid && !dut.o_write && dut.i_accepted)
                  ##1 dut.wait_rdata_valid_r [*1:$] ##1 dut.i_rdata_valid ##1 !dut.wait_rdata_valid_r);

  cover property (f_past_valid && dut.wbuf_used_r==0 && dut.in_wreq && dut.o_ack);

  cover property (f_past_valid && dut.busy_reading_r ##1 (dut.in_wreq && !dut.o_ack));

endmodule

bind wishbone_buf wishbone_buf_sva u_wishbone_buf_sva();