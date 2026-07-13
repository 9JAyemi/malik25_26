module ex_mem_sva (
    input logic clk,
    input logic s7_idex,
    input logic dmem_wen_idex,
    input logic rf_wen_idex,
    input logic branch2_idex,
    input logic mem2reg_idex,
    input logic [15:0] aluout,
    input logic [2:0] flag,
    input logic [15:0] extended_16_idex,
    input logic [15:0] rdata2_idex,
    input logic [3:0] rf_waddr,
    input logic dmem_wen_exmem,
    input logic rf_wen_exmem,
    input logic branch2_exmem,
    input logic mem2reg_exmem,
    input logic [15:0] aluout_exmem,
    input logic [2:0] flag_exmem,
    input logic [15:0] rdata2_exmem,
    input logic [3:0] rf_waddr_exmem,
    input logic [15:0] extended_exmem,
    input logic s7_exmem,
    input logic [15:0] branch_target_final_muxout,
    input logic [15:0] branch_target_exmem,
    input logic nop_lw_idex,
    input logic nop_sw_idex,
    input logic nop_lw_exmem,
    input logic nop_sw_exmem,
    input logic [15:0] pc_added_idex,
    input logic [15:0] pc_added_exmem,
    input logic jal_idex,
    input logic jal_exmem
);

    // dmem_wen_exmem is the prior-cycle dmem_wen_idex.
    check_dmem_wen_capture: assert property (
        @(posedge clk)
        1'b1 |=> (dmem_wen_exmem == $past(dmem_wen_idex))
    );

    // rf_wen_exmem is the prior-cycle rf_wen_idex.
    check_rf_wen_capture: assert property (
        @(posedge clk)
        1'b1 |=> (rf_wen_exmem == $past(rf_wen_idex))
    );

    // branch2_exmem is the prior-cycle branch2_idex.
    check_branch2_capture: assert property (
        @(posedge clk)
        1'b1 |=> (branch2_exmem == $past(branch2_idex))
    );

    // mem2reg_exmem is the prior-cycle mem2reg_idex.
    check_mem2reg_capture: assert property (
        @(posedge clk)
        1'b1 |=> (mem2reg_exmem == $past(mem2reg_idex))
    );

    // aluout_exmem is the prior-cycle aluout.
    check_aluout_capture: assert property (
        @(posedge clk)
        1'b1 |=> (aluout_exmem == $past(aluout))
    );

    // flag_exmem is the prior-cycle flag.
    check_flag_capture: assert property (
        @(posedge clk)
        1'b1 |=> (flag_exmem == $past(flag))
    );

    // rdata2_exmem is the prior-cycle rdata2_idex.
    check_rdata2_capture: assert property (
        @(posedge clk)
        1'b1 |=> (rdata2_exmem == $past(rdata2_idex))
    );

    // rf_waddr_exmem is the prior-cycle rf_waddr.
    check_rf_waddr_capture: assert property (
        @(posedge clk)
        1'b1 |=> (rf_waddr_exmem == $past(rf_waddr))
    );

    // s7_exmem is the prior-cycle s7_idex.
    check_s7_capture: assert property (
        @(posedge clk)
        1'b1 |=> (s7_exmem == $past(s7_idex))
    );

    // extended_exmem is the prior-cycle extended_16_idex.
    check_extended_capture: assert property (
        @(posedge clk)
        1'b1 |=> (extended_exmem == $past(extended_16_idex))
    );

    // branch_target_exmem is the prior-cycle branch_target_final_muxout.
    check_branch_target_capture: assert property (
        @(posedge clk)
        1'b1 |=> (branch_target_exmem == $past(branch_target_final_muxout))
    );

    // nop_lw_exmem is the prior-cycle nop_lw_idex.
    check_nop_lw_capture: assert property (
        @(posedge clk)
        1'b1 |=> (nop_lw_exmem == $past(nop_lw_idex))
    );

    // nop_sw_exmem is the prior-cycle nop_sw_idex.
    check_nop_sw_capture: assert property (
        @(posedge clk)
        1'b1 |=> (nop_sw_exmem == $past(nop_sw_idex))
    );

    // pc_added_exmem is the prior-cycle pc_added_idex.
    check_pc_added_capture: assert property (
        @(posedge clk)
        1'b1 |=> (pc_added_exmem == $past(pc_added_idex))
    );

    // jal_exmem is the prior-cycle jal_idex.
    check_jal_capture: assert property (
        @(posedge clk)
        1'b1 |=> (jal_exmem == $past(jal_idex))
    );

endmodule