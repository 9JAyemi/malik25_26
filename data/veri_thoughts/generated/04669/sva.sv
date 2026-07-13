module EXMEM_Stage_sva (
    input logic        clock,
    input logic        reset,
    input logic        EX_Flush,
    input logic        EX_Stall,
    input logic        M_Stall,
    input logic        EX_Movn,
    input logic        EX_Movz,
    input logic        EX_BZero,
    input logic        EX_RegWrite,
    input logic        EX_MemtoReg,
    input logic        EX_ReverseEndian,
    input logic        EX_LLSC,
    input logic        EX_MemRead,
    input logic        EX_MemWrite,
    input logic        EX_MemByte,
    input logic        EX_MemHalf,
    input logic        EX_MemSignExtend,
    input logic        EX_Left,
    input logic        EX_Right,
    input logic        EX_KernelMode,
    input logic [31:0] EX_RestartPC,
    input logic        EX_IsBDS,
    input logic        EX_Trap,
    input logic        EX_TrapCond,
    input logic        EX_M_CanErr,
    input logic [31:0] EX_ALU_Result,
    input logic [31:0] EX_ReadData2,
    input logic [4:0]  EX_RtRd,
    input logic        M_RegWrite,
    input logic        M_MemtoReg,
    input logic        M_ReverseEndian,
    input logic        M_LLSC,
    input logic        M_MemRead,
    input logic        M_MemWrite,
    input logic        M_MemByte,
    input logic        M_MemHalf,
    input logic        M_MemSignExtend,
    input logic        M_Left,
    input logic        M_Right,
    input logic        M_KernelMode,
    input logic [31:0] M_RestartPC,
    input logic        M_IsBDS,
    input logic        M_Trap,
    input logic        M_TrapCond,
    input logic        M_M_CanErr,
    input logic [31:0] M_ALU_Result,
    input logic [31:0] M_ReadData2,
    input logic [4:0]  M_RtRd,
    input logic        vote_M_RegWrite,
    input logic        vote_M_MemtoReg,
    input logic        vote_M_ReverseEndian,
    input logic        vote_M_LLSC,
    input logic        vote_M_MemRead,
    input logic        vote_M_MemWrite,
    input logic        vote_M_MemByte,
    input logic        vote_M_MemHalf,
    input logic        vote_M_MemSignExtend,
    input logic        vote_M_Left,
    input logic        vote_M_Right,
    input logic        vote_M_KernelMode,
    input logic [31:0] vote_M_RestartPC,
    input logic        vote_M_IsBDS,
    input logic        vote_M_Trap,
    input logic        vote_M_TrapCond,
    input logic        vote_M_M_CanErr,
    input logic [31:0] vote_M_ALU_Result,
    input logic [31:0] vote_M_ReadData2,
    input logic [4:0]  vote_M_RtRd
);

    // Reset clears all scalar control outputs.
    reset_clears_control_outputs: assert property (
        @(posedge clock)
        reset |=> (
            (vote_M_RegWrite      == 1'b0) &&
            (vote_M_MemtoReg      == 1'b0) &&
            (vote_M_ReverseEndian == 1'b0) &&
            (vote_M_LLSC          == 1'b0) &&
            (vote_M_MemRead       == 1'b0) &&
            (vote_M_MemWrite      == 1'b0) &&
            (vote_M_MemByte       == 1'b0) &&
            (vote_M_MemHalf       == 1'b0) &&
            (vote_M_MemSignExtend == 1'b0) &&
            (vote_M_Left          == 1'b0) &&
            (vote_M_Right         == 1'b0) &&
            (vote_M_KernelMode    == 1'b0) &&
            (vote_M_IsBDS         == 1'b0) &&
            (vote_M_Trap          == 1'b0) &&
            (vote_M_TrapCond      == 1'b0) &&
            (vote_M_M_CanErr      == 1'b0)
        )
    );

    // Reset clears all datapath outputs.
    reset_clears_data_outputs: assert property (
        @(posedge clock)
        reset |=> (
            (vote_M_RestartPC  == 32'b0) &&
            (vote_M_ALU_Result == 32'b0) &&
            (vote_M_ReadData2  == 32'b0) &&
            (vote_M_RtRd       == 5'b0)
        )
    );

    // M_Stall selects the M-stage scalar control inputs.
    m_stall_selects_control_outputs: assert property (
        @(posedge clock) disable iff (reset)
        M_Stall |=> (
            (vote_M_RegWrite      == $past(M_RegWrite)) &&
            (vote_M_MemtoReg      == $past(M_MemtoReg)) &&
            (vote_M_ReverseEndian == $past(M_ReverseEndian)) &&
            (vote_M_LLSC          == $past(M_LLSC)) &&
            (vote_M_MemRead       == $past(M_MemRead)) &&
            (vote_M_MemWrite      == $past(M_MemWrite)) &&
            (vote_M_MemByte       == $past(M_MemByte)) &&
            (vote_M_MemHalf       == $past(M_MemHalf)) &&
            (vote_M_MemSignExtend == $past(M_MemSignExtend)) &&
            (vote_M_Left          == $past(M_Left)) &&
            (vote_M_Right         == $past(M_Right)) &&
            (vote_M_KernelMode    == $past(M_KernelMode)) &&
            (vote_M_IsBDS         == $past(M_IsBDS)) &&
            (vote_M_Trap          == $past(M_Trap)) &&
            (vote_M_TrapCond      == $past(M_TrapCond)) &&
            (vote_M_M_CanErr      == $past(M_M_CanErr))
        )
    );

    // M_Stall selects the M-stage datapath inputs.
    m_stall_selects_data_outputs: assert property (
        @(posedge clock) disable iff (reset)
        M_Stall |=> (
            (vote_M_RestartPC  == $past(M_RestartPC)) &&
            (vote_M_ALU_Result == $past(M_ALU_Result)) &&
            (vote_M_ReadData2  == $past(M_ReadData2)) &&
            (vote_M_RtRd       == $past(M_RtRd))
        )
    );

    // Without M_Stall, unconditional control fields pass from EX.
    no_m_stall_passes_unconditional_controls: assert property (
        @(posedge clock) disable iff (reset)
        !M_Stall |=> (
            (vote_M_MemtoReg      == $past(EX_MemtoReg)) &&
            (vote_M_ReverseEndian == $past(EX_ReverseEndian)) &&
            (vote_M_LLSC          == $past(EX_LLSC)) &&
            (vote_M_MemByte       == $past(EX_MemByte)) &&
            (vote_M_MemHalf       == $past(EX_MemHalf)) &&
            (vote_M_MemSignExtend == $past(EX_MemSignExtend)) &&
            (vote_M_Left          == $past(EX_Left)) &&
            (vote_M_Right         == $past(EX_Right)) &&
            (vote_M_KernelMode    == $past(EX_KernelMode)) &&
            (vote_M_IsBDS         == $past(EX_IsBDS)) &&
            (vote_M_TrapCond      == $past(EX_TrapCond))
        )
    );

    // Without M_Stall, datapath fields pass from EX.
    no_m_stall_passes_data_fields: assert property (
        @(posedge clock) disable iff (reset)
        !M_Stall |=> (
            (vote_M_RestartPC  == $past(EX_RestartPC)) &&
            (vote_M_ALU_Result == $past(EX_ALU_Result)) &&
            (vote_M_ReadData2  == $past(EX_ReadData2)) &&
            (vote_M_RtRd       == $past(EX_RtRd))
        )
    );

    // EX stall or flush clears the flush-sensitive controls when not M_Stall.
    bubble_clears_flush_sensitive_controls: assert property (
        @(posedge clock) disable iff (reset)
        (!M_Stall && (EX_Stall || EX_Flush)) |=> (
            (vote_M_RegWrite == 1'b0) &&
            (vote_M_MemRead  == 1'b0) &&
            (vote_M_MemWrite == 1'b0) &&
            (vote_M_Trap     == 1'b0) &&
            (vote_M_M_CanErr == 1'b0)
        )
    );

    // Without bubble insertion, flush-sensitive controls pass from EX.
    no_bubble_passes_flush_sensitive_controls: assert property (
        @(posedge clock) disable iff (reset)
        (!M_Stall && !EX_Stall && !EX_Flush) |=> (
            (vote_M_MemRead  == $past(EX_MemRead)) &&
            (vote_M_MemWrite == $past(EX_MemWrite)) &&
            (vote_M_Trap     == $past(EX_Trap)) &&
            (vote_M_M_CanErr == $past(EX_M_CanErr))
        )
    );

    // Without MOVN/MOVZ handling, RegWrite passes from EX.
    no_bubble_no_movc_passes_regwrite: assert property (
        @(posedge clock) disable iff (reset)
        (!M_Stall && !EX_Stall && !EX_Flush && !(EX_Movn || EX_Movz)) |=> (
            vote_M_RegWrite == $past(EX_RegWrite)
        )
    );

    // With MOVN/MOVZ handling, RegWrite follows the implemented move condition.
    no_bubble_movc_gates_regwrite: assert property (
        @(posedge clock) disable iff (reset)
        (!M_Stall && !EX_Stall && !EX_Flush && (EX_Movn || EX_Movz)) |=> (
            vote_M_RegWrite == (($past(EX_Movn) && !$past(EX_BZero)) || ($past(EX_Movz) && $past(EX_BZero)))
        )
    );

endmodule