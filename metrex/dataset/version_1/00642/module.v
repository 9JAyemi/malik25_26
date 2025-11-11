module MIPS_CPU_CONTROL_UNIT_0_1 (
    input wire [5:0] op,
    input wire [5:0] func,
    input wire z,
    output wire wreg,
    output wire regrt,
    output wire jal,
    output wire m2reg,
    output wire shfit,
    output wire aluimm,
    output wire sext,
    output wire wmem,
    output wire [3:0] aluc,
    output wire [1:0] pcsource
);

    // Instantiate the CONTROL_UNIT without parameter passing since the commands are hardcoded
    CONTROL_UNIT control_unit_inst (
        .op(op),
        .func(func),
        .z(z),
        .wreg(wreg),
        .regrt(regrt),
        .jal(jal),
        .m2reg(m2reg),
        .shfit(shfit),
        .aluimm(aluimm),
        .sext(sext),
        .wmem(wmem),
        .aluc(aluc),
        .pcsource(pcsource)
    );
endmodule


module CONTROL_UNIT (
    input wire [5:0] op,
    input wire [5:0] func,
    input wire z,
    output wire wreg,
    output wire regrt,
    output wire jal,
    output wire m2reg,
    output wire shfit,
    output wire aluimm,
    output wire sext,
    output wire wmem,
    output wire [3:0] aluc,
    output wire [1:0] pcsource
);

    // Corrected control logic implementation based on MIPS instruction formats
    assign wreg = ~op[5] | (op == 6'b100011); // R-type or lw
    assign regrt = op[5] & ~op[2]; // I-type instructions
    assign jal = (op == 6'b000011); // jal
    assign m2reg = (op == 6'b100011); // lw
    assign shfit = (func == 6'b000000) & ~op[5]; // sll, srl, sra for R-type
    assign aluimm = op[5] & ~op[3]; // I-type ALU instructions
    assign sext = ~(op[5] & op[3]); // Sign extend except for lui
    assign wmem = (op == 6'b101011); // sw
    assign aluc[3] = (func == 6'b000011) & ~op[5]; // sra for R-type
    assign aluc[2] = ((op == 6'b000100) & z) | ((op == 6'b000101) & ~z); // beq, bne
    assign aluc[1:0] = (op[5:3] == 3'b000) ? func[1:0] : op[1:0]; // Least significant bits of func or op
    assign pcsource[1] = (op == 6'b000010) | (op == 6'b000011); // j, jal
    assign pcsource[0] = (op == 6'b000100) & z | (op == 6'b000101) & ~z; // beq, bne

endmodule
