// SVA for fifo_buffer
// Focused, concise checks + key coverage
module fifo_buffer_sva;
  // Bound into fifo_buffer scope; accesses internals directly
  default clocking cb @(posedge clock); endclocking
  default disable iff (!aclr);

  // Reset behavior holds during reset
  a_reset_hold: assert property (!aclr |-> (usedw_reg==0 && q_reg==0 && wr_en==0 && rd_en==0));

  // Outputs match internal regs
  a_q_passthrough:     assert property (q == q_reg);
  a_usedw_passthrough: assert property (usedw == usedw_reg);

  // Write/read enable definitions (registered from previous cycle)
  a_wr_en_def: assert property (wr_en == ($past(wrreq) && ($past(usedw_reg) < 32)));
  a_rd_en_def: assert property (rd_en == ($past(rdreq) && ($past(usedw_reg) > 0)));

  // No read when empty (prev cycle)
  a_no_read_when_empty: assert property (($past(usedw_reg)==0 && $past(rdreq)) |-> !rd_en);

  // usedw range and step/update relation (3-cycle pipeline)
  a_usedw_range: assert property (usedw_reg inside {[0:31]});
  a_usedw_update_3cy: assert property (usedw_reg == $past(usedw_reg,3) + $past(wr_en,3) - $past(rd_en,3));
  a_usedw_step_3cy:   assert property (
                        (usedw_reg == $past(usedw_reg,3)) ||
                        (usedw_reg == $past(usedw_reg,3)+1) ||
                        (usedw_reg == $past(usedw_reg,3)-1)
                      );

  // q is a 3-cycle pipeline of buffer[0]
  a_q_pipeline_3cy: assert property (q == $past(buffer[0],3));

  // Memory side-effects: writes and reads target the intended slots (indexes sampled from previous cycle)
  a_write_to_buf0_when_empty: assert property (wr_en && ($past(usedw_reg)==0) |-> buffer[0] == data);
  a_write_places_data_at_idx: assert property (wr_en && ($past(usedw_reg)>0) |-> buffer[$past(usedw_reg)] == data);
  a_read_clears_slot:         assert property (rd_en && ($past(usedw_reg)>1) |-> buffer[$past(usedw_reg)-1] == '0);

  // Coverage
  c_empty:     cover property (usedw_reg==0);
  c_fullish:   cover property (usedw_reg==31);
  c_push_pop:  cover property (wr_en ##1 wr_en ##1 rd_en);
  c_simul:     cover property (wr_en && rd_en);
  c_reset_seq: cover property ($rose(aclr) ##1 wr_en ##[1:10] rd_en);
endmodule

bind fifo_buffer fifo_buffer_sva sva_inst();