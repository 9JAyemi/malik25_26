// SVA for module pipeline
module pipeline_sva;
  // Clocking and safe $past usage across reset
  bit past_valid;
  always_ff @(posedge clk) past_valid <= reset ? 1'b0 : 1'b1;
  default clocking cb @(posedge clk); endclocking
  default disable iff (reset || !past_valid)

  // Stage legality and transitions
  a_stage_range: assert property (stage_reg inside {2'd0,2'd1,2'd2});
  a_stage_0to1:  assert property (stage_reg==2'd0 |=> stage_reg==2'd1);
  a_stage_1to2:  assert property (stage_reg==2'd1 |=> stage_reg==2'd2);
  a_stage_2to0:  assert property (stage_reg==2'd2 |=> stage_reg==2'd0);
  a_stage_known: assert property (!$isunknown(stage_reg));

  // Reset state
  a_reset_state: assert property (@(posedge clk) reset |=> pc==32'd0 && instruction_reg==32'd0 &&
                                                alu_result==32'd0 && data2_reg==32'd0 &&
                                                rs1_reg==5'd0 && rs2_reg==5'd0 && rd_reg==5'd0 &&
                                                stage_reg==2'd0);

  // PC behavior
  a_pc_inc:  assert property (stage_reg==2'd0 |=> pc==$past(pc)+32'd1);
  a_pc_hold: assert property (stage_reg!=2'd0 |=> pc==$past(pc));

  // Instruction fetch/hold
  a_if_instr:   assert property (stage_reg==2'd0 |=> instruction_reg==$past(instruction));
  a_instr_hold: assert property (stage_reg!=2'd0 |=> instruction_reg==$past(instruction_reg));

  // Decode captures and index range
  a_id_caps:       assert property (stage_reg==2'd1 |=> rs1_reg==$past(rs1) && rs2_reg==$past(rs2) &&
                                                     rd_reg==$past(rd)   && data2_reg==$past(data2));
  a_idx_in_range:  assert property (rs1_reg[4]==1'b0 && rs2_reg[4]==1'b0 && rd_reg[4]==1'b0);

  // ALU operations (RTL uses previous data2_reg)
  a_alu_add: assert property (stage_reg==2'd1 && instruction_reg[7:0]==8'h00 |=> alu_result == $past(data1) + $past(data2_reg));
  a_alu_sub: assert property (stage_reg==2'd1 && instruction_reg[7:0]==8'h01 |=> alu_result == $past(data1) - $past(data2_reg));
  a_alu_and: assert property (stage_reg==2'd1 && instruction_reg[7:0]==8'h02 |=> alu_result == ($past(data1) & $past(data2_reg)));
  a_alu_or:  assert property (stage_reg==2'd1 && instruction_reg[7:0]==8'h03 |=> alu_result == ($past(data1) | $past(data2_reg)));
  a_alu_xor: assert property (stage_reg==2'd1 && instruction_reg[7:0]==8'h04 |=> alu_result == ($past(data1) ^ $past(data2_reg)));
  a_alu_not: assert property (stage_reg==2'd1 && instruction_reg[7:0]==8'h05 |=> alu_result == ~($past(data1)));
  a_alu_sll: assert property (stage_reg==2'd1 && instruction_reg[7:0]==8'h06 |=> alu_result == ($past(data1) << $past(data2_reg)));
  a_alu_srl: assert property (stage_reg==2'd1 && instruction_reg[7:0]==8'h07 |=> alu_result == ($past(data1) >> $past(data2_reg)));
  a_alu_def: assert property (stage_reg==2'd1 && !(instruction_reg[7:0] inside {8'h00,8'h01,8'h02,8'h03,8'h04,8'h05,8'h06,8'h07})
                             |=> alu_result == 32'd0);

  // Writeback checks
  a_wb_update: assert property (stage_reg==2'd2 |=> regfile[$past(rd_reg)] == $past(alu_result));
  genvar i;
  generate
    for (i=0;i<16;i++) begin : g_rf_hold
      a_rf_hold: assert property (stage_reg!=2'd2 |=> regfile[i] == $past(regfile[i]));
    end
  endgenerate

  // Outputs reflect regfile
  a_rf_out_0:  assert property (regfile_0  == regfile[0]);
  a_rf_out_1:  assert property (regfile_1  == regfile[1]);
  a_rf_out_2:  assert property (regfile_2  == regfile[2]);
  a_rf_out_3:  assert property (regfile_3  == regfile[3]);
  a_rf_out_4:  assert property (regfile_4  == regfile[4]);
  a_rf_out_5:  assert property (regfile_5  == regfile[5]);
  a_rf_out_6:  assert property (regfile_6  == regfile[6]);
  a_rf_out_7:  assert property (regfile_7  == regfile[7]);
  a_rf_out_8:  assert property (regfile_8  == regfile[8]);
  a_rf_out_9:  assert property (regfile_9  == regfile[9]);
  a_rf_out_10: assert property (regfile_10 == regfile[10]);
  a_rf_out_11: assert property (regfile_11 == regfile[11]);
  a_rf_out_12: assert property (regfile_12 == regfile[12]);
  a_rf_out_13: assert property (regfile_13 == regfile[13]);
  a_rf_out_14: assert property (regfile_14 == regfile[14]);
  a_rf_out_15: assert property (regfile_15 == regfile[15]);

  // Coverage
  c_reset:       cover property (@(posedge clk) reset);
  c_full_cycle:  cover property (stage_reg==2'd0 ##1 stage_reg==2'd1 ##1 stage_reg==2'd2 ##1 stage_reg==2'd0);
  c_add: cover property (stage_reg==2'd1 && instruction_reg[7:0]==8'h00);
  c_sub: cover property (stage_reg==2'd1 && instruction_reg[7:0]==8'h01);
  c_and: cover property (stage_reg==2'd1 && instruction_reg[7:0]==8'h02);
  c_or:  cover property (stage_reg==2'd1 && instruction_reg[7:0]==8'h03);
  c_xor: cover property (stage_reg==2'd1 && instruction_reg[7:0]==8'h04);
  c_not: cover property (stage_reg==2'd1 && instruction_reg[7:0]==8'h05);
  c_sll: cover property (stage_reg==2'd1 && instruction_reg[7:0]==8'h06);
  c_srl: cover property (stage_reg==2'd1 && instruction_reg[7:0]==8'h07);
  generate
    for (i=0;i<16;i++) begin : g_wb_cov
      c_wb_each_reg: cover property (stage_reg==2'd2 && $past(rd_reg)==i[4:0]);
    end
  endgenerate
endmodule

bind pipeline pipeline_sva sva_inst();