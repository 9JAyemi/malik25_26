module hazard_unit_sva (
    input logic CLK,
    input logic RESETn,
    input logic [4:0] rs_ex_mem_hz_i,
    input logic [4:0] rt_ex_mem_hz_i,
    input logic [4:0] rd_mem_wb_hz_i,
    input logic [4:0] rd_wb_ret_hz_i,
    input logic       mem_to_reg_ex_mem_hz_i,
    input logic       reg_wr_mem_wb_hz_i,
    input logic       reg_wr_wb_ret_hz_i,
    input logic       branch_taken_ex_mem_hz_i,
    input logic       jump_iss_ex_hz_i,
    input logic       brn_pred_ex_mem_hz_i,
    input logic       stall_fetch_hz_o,
    input logic       stall_iss_hz_o,
    input logic       flush_ex_hz_o,
    input logic       flush_iss_hz_o,
    input logic [1:0] fwd_p1_ex_mem_hz_o,
    input logic [1:0] fwd_p2_ex_mem_hz_o
);
    ///// Stall outputs /////
    // stall_fetch_hz_o is always 0.
    check_stall_fetch_const_zero: assert property (
        @(posedge CLK) disable iff (!RESETn) (stall_fetch_hz_o == 1'b0)
    );
    // stall_iss_hz_o is always 0.
    check_stall_iss_const_zero: assert property (
        @(posedge CLK) disable iff (!RESETn) (stall_iss_hz_o == 1'b0)
    );

    ///// Flush logic /////
    // flush_ex_hz_o equals branch_taken_ex_mem_hz_i & ~brn_pred_ex_mem_hz_i.
    check_flush_ex_definition: assert property (
        @(posedge CLK) disable iff (!RESETn)
            (flush_ex_hz_o == (branch_taken_ex_mem_hz_i & ~brn_pred_ex_mem_hz_i))
    );
    // flush_iss_hz_o equals (branch_taken_ex_mem_hz_i & ~brn_pred_ex_mem_hz_i) | jump_iss_ex_hz_i.
    check_flush_iss_definition: assert property (
        @(posedge CLK) disable iff (!RESETn)
            (flush_iss_hz_o == ((branch_taken_ex_mem_hz_i & ~brn_pred_ex_mem_hz_i) | jump_iss_ex_hz_i))
    );
    // flush_ex implies taken and mispredicted.
    check_flush_ex_implies_taken_mispred: assert property (
        @(posedge CLK) disable iff (!RESETn)
            (flush_ex_hz_o |-> (branch_taken_ex_mem_hz_i && !brn_pred_ex_mem_hz_i))
    );
    // flush_ex implies flush_iss (since flush_iss = flush_ex | jump).
    check_flush_ex_implies_flush_iss: assert property (
        @(posedge CLK) disable iff (!RESETn)
            (flush_ex_hz_o |-> flush_iss_hz_o)
    );
    // jump sets flush_iss.
    check_jump_sets_flush_iss: assert property (
        @(posedge CLK) disable iff (!RESETn)
            (jump_iss_ex_hz_i |-> flush_iss_hz_o)
    );

    ///// Forwarding for operand 1 (rs_ex_mem_hz_i) /////
    // If MEM/WB writes matching nonzero rd, select 2'b10.
    check_fwd_p1_memwb_select: assert property (
        @(posedge CLK) disable iff (!RESETn)
            ((reg_wr_mem_wb_hz_i && (|rd_mem_wb_hz_i) && (rd_mem_wb_hz_i == rs_ex_mem_hz_i))
             |-> (fwd_p1_ex_mem_hz_o == 2'b10))
    );
    // If MEM/WB is not selected and WB/RET writes matching nonzero rd, select 2'b01.
    check_fwd_p1_wbret_select: assert property (
        @(posedge CLK) disable iff (!RESETn)
            ((!(reg_wr_mem_wb_hz_i && (|rd_mem_wb_hz_i) && (rd_mem_wb_hz_i == rs_ex_mem_hz_i)) &&
               (reg_wr_wb_ret_hz_i && (|rd_wb_ret_hz_i) && (rd_wb_ret_hz_i == rs_ex_mem_hz_i)))
             |-> (fwd_p1_ex_mem_hz_o == 2'b01))
    );
    // If neither source matches, select 2'b00.
    check_fwd_p1_default_zero: assert property (
        @(posedge CLK) disable iff (!RESETn)
            ((!(reg_wr_mem_wb_hz_i && (|rd_mem_wb_hz_i) && (rd_mem_wb_hz_i == rs_ex_mem_hz_i)) &&
               !(reg_wr_wb_ret_hz_i && (|rd_wb_ret_hz_i) && (rd_wb_ret_hz_i == rs_ex_mem_hz_i)))
             |-> (fwd_p1_ex_mem_hz_o == 2'b00))
    );
    // If 2'b10 is selected, MEM/WB match condition holds.
    check_fwd_p1_when_10_implies_memwb: assert property (
        @(posedge CLK) disable iff (!RESETn)
            ((fwd_p1_ex_mem_hz_o == 2'b10)
             |-> (reg_wr_mem_wb_hz_i && (|rd_mem_wb_hz_i) && (rd_mem_wb_hz_i == rs_ex_mem_hz_i)))
    );
    // If 2'b01 is selected, MEM/WB not selected and WB/RET match holds.
    check_fwd_p1_when_01_implies_wbret: assert property (
        @(posedge CLK) disable iff (!RESETn)
            ((fwd_p1_ex_mem_hz_o == 2'b01)
             |-> (!(reg_wr_mem_wb_hz_i && (|rd_mem_wb_hz_i) && (rd_mem_wb_hz_i == rs_ex_mem_hz_i)) &&
                  (reg_wr_wb_ret_hz_i && (|rd_wb_ret_hz_i) && (rd_wb_ret_hz_i == rs_ex_mem_hz_i))))
    );
    // If 2'b00 is selected, neither match holds.
    check_fwd_p1_when_00_implies_none: assert property (
        @(posedge CLK) disable iff (!RESETn)
            ((fwd_p1_ex_mem_hz_o == 2'b00)
             |-> (!(reg_wr_mem_wb_hz_i && (|rd_mem_wb_hz_i) && (rd_mem_wb_hz_i == rs_ex_mem_hz_i)) &&
                  !(reg_wr_wb_ret_hz_i && (|rd_wb_ret_hz_i) && (rd_wb_ret_hz_i == rs_ex_mem_hz_i))))
    );
    // fwd_p1 encoding never 2'b11.
    check_fwd_p1_never_11: assert property (
        @(posedge CLK) disable iff (!RESETn)
            (fwd_p1_ex_mem_hz_o inside {2'b00,2'b01,2'b10})
    );

    ///// Forwarding for operand 2 (rt_ex_mem_hz_i) /////
    // If MEM/WB writes matching nonzero rd, select 2'b10.
    check_fwd_p2_memwb_select: assert property (
        @(posedge CLK) disable iff (!RESETn)
            ((reg_wr_mem_wb_hz_i && (|rd_mem_wb_hz_i) && (rd_mem_wb_hz_i == rt_ex_mem_hz_i))
             |-> (fwd_p2_ex_mem_hz_o == 2'b10))
    );
    // If MEM/WB is not selected and WB/RET writes matching nonzero rd, select 2'b01.
    check_fwd_p2_wbret_select: assert property (
        @(posedge CLK) disable iff (!RESETn)
            ((!(reg_wr_mem_wb_hz_i && (|rd_mem_wb_hz_i) && (rd_mem_wb_hz_i == rt_ex_mem_hz_i)) &&
               (reg_wr_wb_ret_hz_i && (|rd_wb_ret_hz_i) && (rd_wb_ret_hz_i == rt_ex_mem_hz_i)))
             |-> (fwd_p2_ex_mem_hz_o == 2'b01))
    );
    // If neither source matches, select 2'b00.
    check_fwd_p2_default_zero: assert property (
        @(posedge CLK) disable iff (!RESETn)
            ((!(reg_wr_mem_wb_hz_i && (|rd_mem_wb_hz_i) && (rd_mem_wb_hz_i == rt_ex_mem_hz_i)) &&
               !(reg_wr_wb_ret_hz_i && (|rd_wb_ret_hz_i) && (rd_wb_ret_hz_i == rt_ex_mem_hz_i)))
             |-> (fwd_p2_ex_mem_hz_o == 2'b00))
    );
    // If 2'b10 is selected, MEM/WB match condition holds.
    check_fwd_p2_when_10_implies_memwb: assert property (
        @(posedge CLK) disable iff (!RESETn)
            ((fwd_p2_ex_mem_hz_o == 2'b10)
             |-> (reg_wr_mem_wb_hz_i && (|rd_mem_wb_hz_i) && (rd_mem_wb_hz_i == rt_ex_mem_hz_i)))
    );
    // If 2'b01 is selected, MEM/WB not selected and WB/RET match holds.
    check_fwd_p2_when_01_implies_wbret: assert property (
        @(posedge CLK) disable iff (!RESETn)
            ((fwd_p2_ex_mem_hz_o == 2'b01)
             |-> (!(reg_wr_mem_wb_hz_i && (|rd_mem_wb_hz_i) && (rd_mem_wb_hz_i == rt_ex_mem_hz_i)) &&
                  (reg_wr_wb_ret_hz_i && (|rd_wb_ret_hz_i) && (rd_wb_ret_hz_i == rt_ex_mem_hz_i))))
    );
    // If 2'b00 is selected, neither match holds.
    check_fwd_p2_when_00_implies_none: assert property (
        @(posedge CLK) disable iff (!RESETn)
            ((fwd_p2_ex_mem_hz_o == 2'b00)
             |-> (!(reg_wr_mem_wb_hz_i && (|rd_mem_wb_hz_i) && (rd_mem_wb_hz_i == rt_ex_mem_hz_i)) &&
                  !(reg_wr_wb_ret_hz_i && (|rd_wb_ret_hz_i) && (rd_wb_ret_hz_i == rt_ex_mem_hz_i))))
    );
    // fwd_p2 encoding never 2'b11.
    check_fwd_p2_never_11: assert property (
        @(posedge CLK) disable iff (!RESETn)
            (fwd_p2_ex_mem_hz_o inside {2'b00,2'b01,2'b10})
    );
endmodule