// SVA bind module for control. Sample on any convenient tb clock.
module control_sva #(parameter REG_ADDR_WIDTH = 5)
(
  input logic clk,
  input logic rst_n
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  // Definition check for internal hazard net
  a_load_hazard_def: assert property (
    load_hazard ==
      ( id_ex_mem_data_rd_en &
        ( ((id_ex_reg_wr_addr == if_id_rd_reg_a_addr) & if_id_rd_reg_a_en) |
          ((id_ex_reg_wr_addr == if_id_rd_reg_b_addr) & if_id_rd_reg_b_en) ) )
  );

  // Functional equivalences (strong, concise)
  a_stall_eq:          assert property (stall         == (!select_new_pc && load_hazard));
  a_gen_flush_eq:      assert property (general_flush ==  select_new_pc);
  a_dec_flush_eq:      assert property (decode_flush  == (select_new_pc || load_hazard));
  a_inst_rd_en_eq:     assert property (inst_rd_en    == (select_new_pc || !load_hazard));

  // Truth-table safety (redundant but explicit)
  a_sel_new_pc:  assert property (select_new_pc                     |->  inst_rd_en && !stall &&  general_flush &&  decode_flush);
  a_hazard:      assert property (!select_new_pc && load_hazard     |-> !inst_rd_en &&  stall && !general_flush &&  decode_flush);
  a_no_hazard:   assert property (!select_new_pc && !load_hazard    |->  inst_rd_en && !stall && !general_flush && !decode_flush);

  // Sanity/X checks
  a_known_outs:    assert property (!$isunknown({inst_rd_en, stall, general_flush, decode_flush}));
  a_known_hazard:  assert property (!$isunknown(load_hazard));
  a_no_stall_with_flush: assert property (!(stall && general_flush));

  // Coverage: all meaningful cases
  c_select_new_pc: cover property (select_new_pc);
  c_hazard_a:      cover property (!select_new_pc && id_ex_mem_data_rd_en &&
                                   if_id_rd_reg_a_en && (id_ex_reg_wr_addr == if_id_rd_reg_a_addr) &&
                                  !if_id_rd_reg_b_en);
  c_hazard_b:      cover property (!select_new_pc && id_ex_mem_data_rd_en &&
                                   if_id_rd_reg_b_en && (id_ex_reg_wr_addr == if_id_rd_reg_b_addr) &&
                                  !if_id_rd_reg_a_en);
  c_hazard_both:   cover property (!select_new_pc && id_ex_mem_data_rd_en &&
                                   if_id_rd_reg_a_en && if_id_rd_reg_b_en &&
                                   (id_ex_reg_wr_addr == if_id_rd_reg_a_addr) &&
                                   (id_ex_reg_wr_addr == if_id_rd_reg_b_addr));
  c_no_hazard:     cover property (!select_new_pc && !load_hazard);

endmodule

// Bind example (hook clk/rst_n from your environment)
bind control control_sva #(.REG_ADDR_WIDTH(REG_ADDR_WIDTH)) u_control_sva (.clk(clk), .rst_n(rst_n));