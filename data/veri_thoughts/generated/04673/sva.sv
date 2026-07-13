module cpu_ctr_sva (
    input logic        clk,
    input logic [5:0]  opcode,
    input logic        RegDst,
    input logic        ALUsrcB,
    input logic        MemToReg,
    input logic        WriteReg,
    input logic        MemWrite,
    input logic        Branch,
    input logic        ALUop1,
    input logic        ALUop0,
    input logic        JMP
);

    // Clock: external sampling clk. Reset: none in RTL. Logic: combinational decode.

    // JMP decodes opcode 000010.
    check_jmp_decode: assert property (
        @(posedge clk) (JMP == (opcode == 6'b000010))
    );

    // RegDst decodes opcode 000000.
    check_regdst_decode: assert property (
        @(posedge clk) (RegDst == (opcode == 6'b000000))
    );

    // MemToReg decodes opcode 100011.
    check_memtoreg_decode: assert property (
        @(posedge clk) (MemToReg == (opcode == 6'b100011))
    );

    // MemWrite decodes opcode 101011.
    check_memwrite_decode: assert property (
        @(posedge clk) (MemWrite == (opcode == 6'b101011))
    );

    // Branch decodes opcode 000100.
    check_branch_decode: assert property (
        @(posedge clk) (Branch == (opcode == 6'b000100))
    );

    // ALUop1 matches the R-type decode.
    check_aluop1_decode: assert property (
        @(posedge clk) (ALUop1 == (opcode == 6'b000000))
    );

    // ALUop0 matches the BEQ decode.
    check_aluop0_decode: assert property (
        @(posedge clk) (ALUop0 == (opcode == 6'b000100))
    );

    // WriteReg is asserted for R-type and LW only.
    check_writereg_decode: assert property (
        @(posedge clk) (WriteReg == ((opcode == 6'b000000) || (opcode == 6'b100011)))
    );

    // ALUsrcB is asserted for LW and SW only.
    check_alusrcb_decode: assert property (
        @(posedge clk) (ALUsrcB == ((opcode == 6'b100011) || (opcode == 6'b101011)))
    );

    // RegDst and ALUop1 are driven by the same decode.
    check_aluop1_matches_regdst: assert property (
        @(posedge clk) (ALUop1 == RegDst)
    );

    // Branch and ALUop0 are driven by the same decode.
    check_aluop0_matches_branch: assert property (
        @(posedge clk) (ALUop0 == Branch)
    );

    // WriteReg is the OR of RegDst and MemToReg.
    check_writereg_relation: assert property (
        @(posedge clk) (WriteReg == (RegDst || MemToReg))
    );

    // ALUsrcB is the OR of MemToReg and MemWrite.
    check_alusrcb_relation: assert property (
        @(posedge clk) (ALUsrcB == (MemToReg || MemWrite))
    );

endmodule