module control_sva (
    input logic clk,
    input logic [5:0] instru,
    input logic RegDest,
    input logic SaltoCond,
    input logic LeerMem,
    input logic MemaReg,
    input logic [1:0] ALUOp,
    input logic EscrMem,
    input logic FuenteALU,
    input logic EscrReg,
    input logic Saltoincond
);
    // Local copies of instruction encodings used in the case statement
    localparam logic [5:0] INSTR_RTYPE = 6'b000000;
    localparam logic [5:0] INSTR_LW    = 6'b100011;
    localparam logic [5:0] INSTR_SW    = 6'b101011;
    localparam logic [5:0] INSTR_BEQ   = 6'b000100;
    localparam logic [5:0] INSTR_111111= 6'b111111;
    localparam logic [5:0] INSTR_111110= 6'b111110;

    ///// Exact decode checks for instructions without Xs /////
    // For 000000, outputs must match 10'b0100_100_010.
    decode_rtype: assert property (
        @(posedge clk) (instru == INSTR_RTYPE) |-> ({Saltoincond,RegDest,FuenteALU,MemaReg,EscrReg,LeerMem,EscrMem,SaltoCond,ALUOp} == 10'b0100_100_010)
    );
    // For 100011, outputs must match 10'b00_1111_0000.
    decode_lw: assert property (
        @(posedge clk) (instru == INSTR_LW) |-> ({Saltoincond,RegDest,FuenteALU,MemaReg,EscrReg,LeerMem,EscrMem,SaltoCond,ALUOp} == 10'b00_1111_0000)
    );
    // For 111111, outputs must match 10'b00_1010_0000.
    decode_111111: assert property (
        @(posedge clk) (instru == INSTR_111111) |-> ({Saltoincond,RegDest,FuenteALU,MemaReg,EscrReg,LeerMem,EscrMem,SaltoCond,ALUOp} == 10'b00_1010_0000)
    );
    // For 111110, outputs must match 10'b00_0000_0101.
    decode_111110: assert property (
        @(posedge clk) (instru == INSTR_111110) |-> ({Saltoincond,RegDest,FuenteALU,MemaReg,EscrReg,LeerMem,EscrMem,SaltoCond,ALUOp} == 10'b00_0000_0101)
    );

    ///// Partial decode checks for instructions with Xs /////
    // For 101011, only defined bits: FUENTEALU=1, ESCRMEM=1, ALUOp=00, SALTOCOND=0, ESCRREG=0, LEERMEM=0, SALTOINCOND=0.
    decode_sw_defined_bits: assert property (
        @(posedge clk) (instru == INSTR_SW) |-> (FuenteALU == 1'b1) && (EscrMem == 1'b1) && (ALUOp == 2'b00) &&
                                           (SaltoCond == 1'b0) && (EscrReg == 1'b0) && (LeerMem == 1'b0) &&
                                           (Saltoincond == 1'b0)
    );
    // For 000100, only defined bits: FUENTEALU=0, SALTOCOND=1, ALUOp=01, ESCRREG=0, LEERMEM=0, ESCRMEM=0, SALTOINCOND=0.
    decode_beq_defined_bits: assert property (
        @(posedge clk) (instru == INSTR_BEQ) |-> (FuenteALU == 1'b0) && (SaltoCond == 1'b1) && (ALUOp == 2'b01) &&
                                         (EscrReg == 1'b0) && (LeerMem == 1'b0) && (EscrMem == 1'b0) &&
                                         (Saltoincond == 1'b0)
    );

    ///// Default decode for all other instructions /////
    // For instructions not listed, outputs must match default 10'b00_1010_0000.
    decode_default_others: assert property (
        @(posedge clk)
        (instru != INSTR_RTYPE) && (instru != INSTR_LW) && (instru != INSTR_SW) &&
        (instru != INSTR_BEQ) && (instru != INSTR_111110) && (instru != INSTR_111111)
        |-> ({Saltoincond,RegDest,FuenteALU,MemaReg,EscrReg,LeerMem,EscrMem,SaltoCond,ALUOp} == 10'b00_1010_0000)
    );

    ///// Global invariants derived from the decode /////
    // Saltoincond is always 0 for all decodes.
    invariant_saltoincond_zero: assert property (
        @(posedge clk) (Saltoincond == 1'b0)
    );
    // If SaltoCond is 1, ALUOp must be 01 and FuenteALU must be 0.
    invariant_branch_flags: assert property (
        @(posedge clk) (SaltoCond == 1'b1) |-> (ALUOp == 2'b01) && (FuenteALU == 1'b0)
    );
    // If ALUOp is 01, SaltoCond must be 1 and FuenteALU must be 0.
    invariant_aluop01_means_branch: assert property (
        @(posedge clk) (ALUOp == 2'b01) |-> (SaltoCond == 1'b1) && (FuenteALU == 1'b0)
    );
    // If FuenteALU is 1, ALUOp must be 00.
    invariant_fuent_to_aluop: assert property (
        @(posedge clk) (FuenteALU == 1'b1) |-> (ALUOp == 2'b00)
    );
    // If EscrMem is 1, then it's a store: FuenteALU=1, ALUOp=00, and no read/branch/regwrite.
    invariant_store_side_effects: assert property (
        @(posedge clk) (EscrMem == 1'b1) |-> (FuenteALU == 1'b1) && (ALUOp == 2'b00) &&
                                           (LeerMem == 1'b0) && (EscrReg == 1'b0) && (SaltoCond == 1'b0)
    );
    // If LeerMem is 1, then it's a load: MemaReg=1, EscrReg=1, FuenteALU=1, ALUOp=00, and no store/branch.
    invariant_load_side_effects: assert property (
        @(posedge clk) (LeerMem == 1'b1) |-> (MemaReg == 1'b1) && (EscrReg == 1'b1) &&
                                          (EscrMem == 1'b0) && (SaltoCond == 1'b0) &&
                                          (FuenteALU == 1'b1) && (ALUOp == 2'b00)
    );
    // If EscrReg is 1, then there is no branch or memory write.
    invariant_regwrite_no_branch_store: assert property (
        @(posedge clk) (EscrReg == 1'b1) |-> (SaltoCond == 1'b0) && (EscrMem == 1'b0)
    );
    // If ALUOp is 10, it's R-type: RegDest=1, EscrReg=1, FUENTEALU=0, no mem or branch.
    invariant_aluop10_rtype: assert property (
        @(posedge clk) (ALUOp == 2'b10) |-> (RegDest == 1'b1) && (EscrReg == 1'b1) && (FuenteALU == 1'b0) &&
                                         (MemaReg == 1'b0) && (LeerMem == 1'b0) && (EscrMem == 1'b0) &&
                                         (SaltoCond == 1'b0)
    );
endmodule