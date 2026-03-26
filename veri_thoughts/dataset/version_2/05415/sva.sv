module branch_hazard_detector_sva (
    input logic        clk,
    input logic [4:0]  ID_rs,
    input logic [4:0]  ID_rt,
    input logic        EX_regwe,
    input logic [4:0]  EX_RW,
    input logic        MEM_ramtoreg,
    input logic [4:0]  MEM_RW,
    input logic        ID_jmp_need_reg,
    input logic        ID_jmp_reg,
    input logic        ID_misprediction,
    input logic        branch_flushD,
    input logic        branch_flushE
);

    // branch_flushD is the OR of jump-register and misprediction.
    check_branch_flushD_equation: assert property (
        @(posedge clk)
        branch_flushD == (ID_jmp_reg || ID_misprediction)
    );

    // A jump-register request forces branch_flushD high.
    check_branch_flushD_on_jmp_reg: assert property (
        @(posedge clk)
        ID_jmp_reg |-> branch_flushD
    );

    // A misprediction forces branch_flushD high.
    check_branch_flushD_on_misprediction: assert property (
        @(posedge clk)
        ID_misprediction |-> branch_flushD
    );

    // branch_flushD is low when neither source requests a flush.
    check_branch_flushD_clear_without_cause: assert property (
        @(posedge clk)
        (!ID_jmp_reg && !ID_misprediction) |-> !branch_flushD
    );

    // branch_flushE matches the implemented EX/MEM hazard expression.
    check_branch_flushE_equation: assert property (
        @(posedge clk)
        branch_flushE == (
            (ID_jmp_need_reg && EX_regwe && (EX_RW != 5'd0) &&
             ((EX_RW == ID_rs) || (EX_RW == ID_rt))) ||
            (ID_jmp_need_reg && MEM_ramtoreg && (MEM_RW != 5'd0) &&
             ((MEM_RW == ID_rs) || (MEM_RW == ID_rt)))
        )
    );

    // An EX-stage register dependency forces branch_flushE high.
    check_branch_flushE_on_ex_dependency: assert property (
        @(posedge clk)
        (ID_jmp_need_reg && EX_regwe && (EX_RW != 5'd0) &&
         ((EX_RW == ID_rs) || (EX_RW == ID_rt))) |-> branch_flushE
    );

    // A MEM-stage load dependency forces branch_flushE high.
    check_branch_flushE_on_mem_dependency: assert property (
        @(posedge clk)
        (ID_jmp_need_reg && MEM_ramtoreg && (MEM_RW != 5'd0) &&
         ((MEM_RW == ID_rs) || (MEM_RW == ID_rt))) |-> branch_flushE
    );

    // branch_flushE can only be high for a real jump-register data hazard.
    check_branch_flushE_implies_valid_dependency: assert property (
        @(posedge clk)
        branch_flushE |-> (
            ID_jmp_need_reg &&
            (
                (EX_regwe && (EX_RW != 5'd0) &&
                 ((EX_RW == ID_rs) || (EX_RW == ID_rt))) ||
                (MEM_ramtoreg && (MEM_RW != 5'd0) &&
                 ((MEM_RW == ID_rs) || (MEM_RW == ID_rt)))
            )
        )
    );

    // branch_flushE is low when neither EX nor MEM hazard condition is present.
    check_branch_flushE_clear_without_dependency: assert property (
        @(posedge clk)
        (!(ID_jmp_need_reg && EX_regwe && (EX_RW != 5'd0) &&
           ((EX_RW == ID_rs) || (EX_RW == ID_rt))) &&
         !(ID_jmp_need_reg && MEM_ramtoreg && (MEM_RW != 5'd0) &&
           ((MEM_RW == ID_rs) || (MEM_RW == ID_rt)))) |-> !branch_flushE
    );

endmodule