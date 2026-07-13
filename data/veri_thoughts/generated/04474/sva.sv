module MEMWB_Stage_sva (
    input logic        clock,
    input logic        reset,
    input logic        M_Flush,
    input logic        M_Stall,
    input logic        WB_Stall,
    input logic        M_RegWrite,
    input logic        M_MemtoReg,
    input logic [31:0] M_ReadData,
    input logic [31:0] M_ALU_Result,
    input logic [4:0]  M_RtRd,
    input logic        WB_RegWrite,
    input logic        WB_MemtoReg,
    input logic [31:0] WB_ReadData,
    input logic [31:0] WB_ALU_Result,
    input logic [4:0]  WB_RtRd,
    input logic        vote_WB_RegWrite,
    input logic        vote_WB_MemtoReg,
    input logic [31:0] vote_WB_ReadData,
    input logic [31:0] vote_WB_ALU_Result,
    input logic [4:0]  vote_WB_RtRd
);

    // Reset clears all pipeline outputs on the next cycle.
    check_reset_clears_outputs: assert property (
        @(posedge clock)
        reset |=> (vote_WB_RegWrite  == 1'b0)  &&
                  (vote_WB_MemtoReg  == 1'b0)  &&
                  (vote_WB_ReadData  == 32'b0) &&
                  (vote_WB_ALU_Result == 32'b0) &&
                  (vote_WB_RtRd      == 5'b0)
    );

    // When WB is not stalled, control outputs capture WB inputs.
    check_wb_capture_control: assert property (
        @(posedge clock) disable iff (reset)
        (!WB_Stall) |=> (vote_WB_RegWrite == $past(WB_RegWrite)) &&
                        (vote_WB_MemtoReg == $past(WB_MemtoReg))
    );

    // When WB is not stalled, data outputs capture WB inputs.
    check_wb_capture_data: assert property (
        @(posedge clock) disable iff (reset)
        (!WB_Stall) |=> (vote_WB_ReadData   == $past(WB_ReadData)) &&
                        (vote_WB_ALU_Result == $past(WB_ALU_Result)) &&
                        (vote_WB_RtRd       == $past(WB_RtRd))
    );

    // When WB is stalled and M is stalled or flushed, control outputs clear.
    check_stall_flush_clear_control: assert property (
        @(posedge clock) disable iff (reset)
        (WB_Stall && (M_Stall || M_Flush)) |=> (vote_WB_RegWrite == 1'b0) &&
                                               (vote_WB_MemtoReg == 1'b0)
    );

    // When WB is stalled and M is stalled or flushed, data outputs clear.
    check_stall_flush_clear_data: assert property (
        @(posedge clock) disable iff (reset)
        (WB_Stall && (M_Stall || M_Flush)) |=> (vote_WB_ReadData   == 32'b0) &&
                                               (vote_WB_ALU_Result == 32'b0) &&
                                               (vote_WB_RtRd       == 5'b0)
    );

    // When only WB is stalled, control outputs capture M-stage inputs.
    check_m_capture_control: assert property (
        @(posedge clock) disable iff (reset)
        (WB_Stall && !M_Stall && !M_Flush) |=> (vote_WB_RegWrite == $past(M_RegWrite)) &&
                                               (vote_WB_MemtoReg == $past(M_MemtoReg))
    );

    // When only WB is stalled, data outputs capture M-stage inputs.
    check_m_capture_data: assert property (
        @(posedge clock) disable iff (reset)
        (WB_Stall && !M_Stall && !M_Flush) |=> (vote_WB_ReadData   == $past(M_ReadData)) &&
                                               (vote_WB_ALU_Result == $past(M_ALU_Result)) &&
                                               (vote_WB_RtRd       == $past(M_RtRd))
    );

endmodule