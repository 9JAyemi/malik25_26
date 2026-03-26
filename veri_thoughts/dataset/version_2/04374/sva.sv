module exin_sva (
    input logic        CCLK,
    input logic        rst,
    input logic [31:0] instr,
    input logic [7:0]  IF
);

    // Reset forces the decode output to zero.
    check_reset_forces_zero: assert property (
        @(posedge CCLK) rst |-> (IF == 8'd0)
    );

    // Unsupported top-level opcodes decode to zero.
    check_default_opcode_zero: assert property (
        @(posedge CCLK) disable iff (rst)
        (!(instr[31:26] inside {
            6'b000000, 6'b001000, 6'b001001, 6'b001100, 6'b001101,
            6'b001110, 6'b001111, 6'b100011, 6'b101011, 6'b000100,
            6'b000101, 6'b001010, 6'b001011, 6'b000010, 6'b000011
        })) |-> (IF == 8'd0)
    );

    // Unsupported R-type funct values decode to zero.
    check_default_rtype_zero: assert property (
        @(posedge CCLK) disable iff (rst)
        ((instr[31:26] == 6'b000000) &&
         !(instr[5:0] inside {
            6'b100000, 6'b100001, 6'b100010, 6'b100011, 6'b100100,
            6'b100101, 6'b100110, 6'b100111, 6'b101010, 6'b101011,
            6'b000000, 6'b000010, 6'b000011, 6'b000100, 6'b000110,
            6'b000111, 6'b001000
         })) |-> (IF == 8'd0)
    );

    // R-type add with nonzero rd maps to IF code 1.
    check_rtype_add_nonzero_rd: assert property (
        @(posedge CCLK) disable iff (rst)
        ((instr[31:26] == 6'b000000) &&
         (instr[5:0] == 6'b100000) &&
         (|instr[15:11])) |-> (IF == 8'd1)
    );

    // R-type add with rd equal to zero maps to IF code 0.
    check_rtype_add_zero_rd: assert property (
        @(posedge CCLK) disable iff (rst)
        ((instr[31:26] == 6'b000000) &&
         (instr[5:0] == 6'b100000) &&
         !(|instr[15:11])) |-> (IF == 8'd0)
    );

    // R-type addu maps to IF code 2.
    check_rtype_addu: assert property (
        @(posedge CCLK) disable iff (rst)
        ((instr[31:26] == 6'b000000) &&
         (instr[5:0] == 6'b100001)) |-> (IF == 8'd2)
    );

    // R-type sub maps to IF code 3.
    check_rtype_sub: assert property (
        @(posedge CCLK) disable iff (rst)
        ((instr[31:26] == 6'b000000) &&
         (instr[5:0] == 6'b100010)) |-> (IF == 8'd3)
    );

    // R-type subu maps to IF code 4.
    check_rtype_subu: assert property (
        @(posedge CCLK) disable iff (rst)
        ((instr[31:26] == 6'b000000) &&
         (instr[5:0] == 6'b100011)) |-> (IF == 8'd4)
    );

    // R-type and maps to IF code 5.
    check_rtype_and: assert property (
        @(posedge CCLK) disable iff (rst)
        ((instr[31:26] == 6'b000000) &&
         (instr[5:0] == 6'b100100)) |-> (IF == 8'd5)
    );

    // R-type or maps to IF code 6.
    check_rtype_or: assert property (
        @(posedge CCLK) disable iff (rst)
        ((instr[31:26] == 6'b000000) &&
         (instr[5:0] == 6'b100101)) |-> (IF == 8'd6)
    );

    // R-type xor maps to IF code 7.
    check_rtype_xor: assert property (
        @(posedge CCLK) disable iff (rst)
        ((instr[31:26] == 6'b000000) &&
         (instr[5:0] == 6'b100110)) |-> (IF == 8'd7)
    );

    // R-type nor maps to IF code 8.
    check_rtype_nor: assert property (
        @(posedge CCLK) disable iff (rst)
        ((instr[31:26] == 6'b000000) &&
         (instr[5:0] == 6'b100111)) |-> (IF == 8'd8)
    );

    // R-type slt maps to IF code 9.
    check_rtype_slt: assert property (
        @(posedge CCLK) disable iff (rst)
        ((instr[31:26] == 6'b000000) &&
         (instr[5:0] == 6'b101010)) |-> (IF == 8'd9)
    );

    // R-type sltu maps to IF code 10.
    check_rtype_sltu: assert property (
        @(posedge CCLK) disable iff (rst)
        ((instr[31:26] == 6'b000000) &&
         (instr[5:0] == 6'b101011)) |-> (IF == 8'd10)
    );

    // R-type sll maps to IF code 11.
    check_rtype_sll: assert property (
        @(posedge CCLK) disable iff (rst)
        ((instr[31:26] == 6'b000000) &&
         (instr[5:0] == 6'b000000)) |-> (IF == 8'd11)
    );

    // R-type srl maps to IF code 12.
    check_rtype_srl: assert property (
        @(posedge CCLK) disable iff (rst)
        ((instr[31:26] == 6'b000000) &&
         (instr[5:0] == 6'b000010)) |-> (IF == 8'd12)
    );

    // R-type sra maps to IF code 13.
    check_rtype_sra: assert property (
        @(posedge CCLK) disable iff (rst)
        ((instr[31:26] == 6'b000000) &&
         (instr[5:0] == 6'b000011)) |-> (IF == 8'd13)
    );

    // R-type sllv maps to IF code 14.
    check_rtype_sllv: assert property (
        @(posedge CCLK) disable iff (rst)
        ((instr[31:26] == 6'b000000) &&
         (instr[5:0] == 6'b000100)) |-> (IF == 8'd14)
    );

    // R-type srlv maps to IF code 15.
    check_rtype_srlv: assert property (
        @(posedge CCLK) disable iff (rst)
        ((instr[31:26] == 6'b000000) &&
         (instr[5:0] == 6'b000110)) |-> (IF == 8'd15)
    );

    // R-type srav maps to IF code 16.
    check_rtype_srav: assert property (
        @(posedge CCLK) disable iff (rst)
        ((instr[31:26] == 6'b000000) &&
         (instr[5:0] == 6'b000111)) |-> (IF == 8'd16)
    );

    // R-type jr maps to IF code 17.
    check_rtype_jr: assert property (
        @(posedge CCLK) disable iff (rst)
        ((instr[31:26] == 6'b000000) &&
         (instr[5:0] == 6'b001000)) |-> (IF == 8'd17)
    );

    // addi maps to IF code 18.
    check_opcode_addi: assert property (
        @(posedge CCLK) disable iff (rst)
        (instr[31:26] == 6'b001000) |-> (IF == 8'd18)
    );

    // addiu maps to IF code 19.
    check_opcode_addiu: assert property (
        @(posedge CCLK) disable iff (rst)
        (instr[31:26] == 6'b001001) |-> (IF == 8'd19)
    );

    // andi maps to IF code 20.
    check_opcode_andi: assert property (
        @(posedge CCLK) disable iff (rst)
        (instr[31:26] == 6'b001100) |-> (IF == 8'd20)
    );

    // ori maps to IF code 15.
    check_opcode_ori: assert property (
        @(posedge CCLK) disable iff (rst)
        (instr[31:26] == 6'b001101) |-> (IF == 8'd15)
    );

    // xori maps to IF code 22.
    check_opcode_xori: assert property (
        @(posedge CCLK) disable iff (rst)
        (instr[31:26] == 6'b001110) |-> (IF == 8'd22)
    );

    // lui maps to IF code 23.
    check_opcode_lui: assert property (
        @(posedge CCLK) disable iff (rst)
        (instr[31:26] == 6'b001111) |-> (IF == 8'd23)
    );

    // lw maps to IF code 24.
    check_opcode_lw: assert property (
        @(posedge CCLK) disable iff (rst)
        (instr[31:26] == 6'b100011) |-> (IF == 8'd24)
    );

    // sw maps to IF code 25.
    check_opcode_sw: assert property (
        @(posedge CCLK) disable iff (rst)
        (instr[31:26] == 6'b101011) |-> (IF == 8'd25)
    );

    // beq maps to IF code 26.
    check_opcode_beq: assert property (
        @(posedge CCLK) disable iff (rst)
        (instr[31:26] == 6'b000100) |-> (IF == 8'd26)
    );

    // bne maps to IF code 27.
    check_opcode_bne: assert property (
        @(posedge CCLK) disable iff (rst)
        (instr[31:26] == 6'b000101) |-> (IF == 8'd27)
    );

    // slti maps to IF code 28.
    check_opcode_slti: assert property (
        @(posedge CCLK) disable iff (rst)
        (instr[31:26] == 6'b001010) |-> (IF == 8'd28)
    );

    // sltiu maps to IF code 29.
    check_opcode_sltiu: assert property (
        @(posedge CCLK) disable iff (rst)
        (instr[31:26] == 6'b001011) |-> (IF == 8'd29)
    );

    // j maps to IF code 30.
    check_opcode_j: assert property (
        @(posedge CCLK) disable iff (rst)
        (instr[31:26] == 6'b000010) |-> (IF == 8'd30)
    );

    // jal maps to IF code 31.
    check_opcode_jal: assert property (
        @(posedge CCLK) disable iff (rst)
        (instr[31:26] == 6'b000011) |-> (IF == 8'd31)
    );

endmodule