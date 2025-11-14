// SVA for smart_unit
// Bind into DUT; references internal signals directly
bind smart_unit smart_unit_asserts u_smart_unit_asserts();

module smart_unit_asserts;

  // Basic tie-offs
  // inst_out/inst_nxt mapping
  assert property (@(posedge clk) inst_out == inst_2);
  assert property (@(posedge clk) inst_nxt == inst_1);

  // apxy_CEN definition
  assert property (@(posedge clk) apxy_CEN == ((addr_inst > 5'd2) && hy_exe));

  // Reset behavior
  assert property (@(posedge clk) !rst_n |-> (inst_1==31'd0 && inst_2==31'd0 && counter==5'd0 && counter_jump==7'd0));
  assert property (@(negedge clk) !rst_n |-> addr_inst==16'd0);

  // addr_inst next-state (latched on negedge)
  // Hold when hy_exe==0
  assert property (@(negedge clk) disable iff (!rst_n)
                   !hy_exe |-> addr_inst == $past(addr_inst));

  // Jump (comp_type_i==5'ha)
  assert property (@(negedge clk) disable iff (!rst_n)
                   (hy_exe && inst_in[30:26]==5'ha && (counter_jump==7'd0))
                   |-> addr_inst == $past(addr_inst) + 5'd1);

  assert property (@(negedge clk) disable iff (!rst_n)
                   (hy_exe && inst_in[30:26]==5'ha && (counter_jump!=7'd0))
                   |-> addr_inst == $past(addr_inst) - inst_in[25:19]);

  // Ready/boot/set increment (priority below jump)
  assert property (@(negedge clk) disable iff (!rst_n)
                   (hy_exe && inst_in[30:26]!=5'ha &&
                    (ready_hy || ($past(addr_inst) < 5'd3) || (inst_1[30:26]==5'h9)))
                   |-> addr_inst == $past(addr_inst) + 5'd1);

  // mov-controlled advance (priority below ready/boot/set)
  assert property (@(negedge clk) disable iff (!rst_n)
                   (hy_exe && inst_in[30:26]!=5'ha &&
                    !(ready_hy || ($past(addr_inst) < 5'd3) || (inst_1[30:26]==5'h9)) &&
                    (inst_1[30:26]==5'h7))
                   |-> addr_inst == (counter==5'd1 ? $past(addr_inst)+5'd1 : $past(addr_inst)));

  // Otherwise hold
  assert property (@(negedge clk) disable iff (!rst_n)
                   (hy_exe && inst_in[30:26]!=5'ha &&
                    !(ready_hy || ($past(addr_inst) < 5'd3) || (inst_1[30:26]==5'h9)) &&
                    (inst_1[30:26]!=5'h7))
                   |-> addr_inst == $past(addr_inst));

  // counter_jump next-state (posedge)
  assert property (@(posedge clk) disable iff (!rst_n)
                   $past(inst_1[30:26]==5'h9) |-> counter_jump == $past(inst_1[25:19]));

  assert property (@(posedge clk) disable iff (!rst_n)
                   $past(inst_in[30:26]==5'ha && counter_jump!=7'd0)
                   |-> counter_jump == $past(counter_jump) - 7'd1);

  assert property (@(posedge clk) disable iff (!rst_n)
                   $past(!(inst_1[30:26]==5'h9) && !(inst_in[30:26]==5'ha && $past(counter_jump)!=7'd0))
                   |-> counter_jump == $past(counter_jump));

  // counter reset outside mov
  assert property (@(posedge clk) disable iff (!rst_n)
                   $past(inst_1[30:26]!=5'h7) |-> counter==5'd0);

  // Write-port ownership under hy_WB && ready_hy (both mov/default agree on W_d1/W_d2)
  assert property (@(posedge clk) disable iff (!rst_n)
                   (inst_out[6] && ready_hy &&  inst_out[5]) |-> (W_d1==1'b1 && W_d2==1'b0));
  assert property (@(posedge clk) disable iff (!rst_n)
                   (inst_out[6] && ready_hy && !inst_out[5]) |-> (W_d1==1'b0 && W_d2==1'b1));

  // Non-mov datapath when hy_WB && ready_hy: addresses and data
  assert property (@(posedge clk) disable iff (!rst_n)
                   (inst_1[30:26]!=5'h7 && inst_out[6] && ready_hy &&  inst_out[5])
                   |-> (addr_d1==inst_in[23:19] && addr_d2==inst_out[4:0] &&
                        Dout_d1==256'd0 && Dout_d2==Din_hy));

  assert property (@(posedge clk) disable iff (!rst_n)
                   (inst_1[30:26]!=5'h7 && inst_out[6] && ready_hy && !inst_out[5])
                   |-> (addr_d1==inst_out[4:0] && addr_d2==inst_in[14:10] &&
                        Dout_d1==Din_hy && Dout_d2==256'd0));

  // Non-mov, no hy writeback path: both write-disabled and zero data
  assert property (@(posedge clk) disable iff (!rst_n)
                   (inst_1[30:26]!=5'h7 && !(inst_out[6] && ready_hy) && ready_hy)
                   |-> (W_d1==1'b1 && W_d2==1'b1 &&
                        addr_d1==inst_in[23:19] && addr_d2==inst_in[14:10] &&
                        Dout_d1==256'd0 && Dout_d2==256'd0));

  assert property (@(posedge clk) disable iff (!rst_n)
                   (inst_1[30:26]!=5'h7 && !(inst_out[6] && ready_hy) && !ready_hy)
                   |-> (W_d1==1'b1 && W_d2==1'b1 &&
                        addr_d1==inst_1[23:19] && addr_d2==inst_1[14:10] &&
                        Dout_d1==256'd0 && Dout_d2==256'd0));

  // mov micro-ops (exclude hy writeback branch)
  // Stage 0: read operands
  assert property (@(posedge clk) disable iff (!rst_n)
                   (inst_1[30:26]==5'h7 && !(inst_out[6] && ready_hy) && counter!=5'd1)
                   |-> (W_d1==1'b1 && W_d2==1'b1 &&
                        addr_d1==inst_1[24:20] && addr_d2==inst_1[24:20] &&
                        Dout_d1==256'd0 && Dout_d2==256'd0));

  // Stage 1: writeback to WB addr, bank by inst_1[19]; data from Cin select by inst_1[25]
  assert property (@(posedge clk) disable iff (!rst_n)
                   (inst_1[30:26]==5'h7 && !(inst_out[6] && ready_hy) && counter==5'd1)
                   |-> (addr_d1==inst_1[18:14] && addr_d2==inst_1[18:14] &&
                        W_d1==inst_1[19] && W_d2==~inst_1[19] &&
                        ((inst_1[25] && (Dout_d1==Din_c2) && (Dout_d2==Din_c2)) ||
                         (!inst_1[25] && (Dout_d1==Din_c1) && (Dout_d2==Din_c1)))));

  // set and jump side-effects
  // set clears inst_2 next cycle
  assert property (@(posedge clk) disable iff (!rst_n)
                   $past(inst_1[30:26]==5'h9) |-> inst_2==31'd0);

  // jump clears inst_1 next cycle
  assert property (@(posedge clk) disable iff (!rst_n)
                   $past(inst_in[30:26]==5'ha) |-> inst_1==31'd0);

  // Coverage
  cover property (@(posedge clk) inst_1[30:26]==5'h7 && counter==5'd0);
  cover property (@(posedge clk) inst_1[30:26]==5'h7 && counter==5'd1);
  cover property (@(negedge clk) hy_exe && inst_in[30:26]==5'ha && counter_jump!=7'd0);
  cover property (@(negedge clk) hy_exe && inst_in[30:26]==5'ha && counter_jump==7'd0);
  cover property (@(posedge clk) inst_1[30:26]==5'h9);
  cover property (@(posedge clk) apxy_CEN);

endmodule