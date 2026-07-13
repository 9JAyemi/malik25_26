module control_sva (
    input logic CLK,
    input logic RESETn,
    input logic [5:0] op,
    input logic [1:0] alu_op,
    input logic regDst,
    input logic aluSrc,
    input logic memToReg,
    input logic regWrite,
    input logic memRead,
    input logic memWrite,
    input logic branch
);
    // regDst mirrors alu_op[1].
    check_regDst_equals_aluop1: assert property (
        @(posedge CLK) disable iff (!RESETn) (regDst == alu_op[1])
    );

    // branch mirrors alu_op[0].
    check_branch_equals_aluop0: assert property (
        @(posedge CLK) disable iff (!RESETn) (branch == alu_op[0])
    );

    // memToReg equals memRead.
    check_memToReg_equals_memRead: assert property (
        @(posedge CLK) disable iff (!RESETn) (memToReg == memRead)
    );

    // aluSrc equals (memRead OR memWrite).
    check_aluSrc_equals_memRead_or_memWrite: assert property (
        @(posedge CLK) disable iff (!RESETn) (aluSrc == (memRead || memWrite))
    );

    // regWrite equals (memToReg OR regDst).
    check_regWrite_equals_memToReg_or_regDst: assert property (
        @(posedge CLK) disable iff (!RESETn) (regWrite == (memToReg || regDst))
    );

    // alu_op bits are mutually exclusive.
    check_aluop_mutex: assert property (
        @(posedge CLK) disable iff (!RESETn) !(alu_op[1] && alu_op[0])
    );

    // memRead and memWrite are mutually exclusive.
    check_mem_mutex: assert property (
        @(posedge CLK) disable iff (!RESETn) !(memRead && memWrite)
    );

    // memToReg implies regWrite.
    check_memToReg_implies_regWrite: assert property (
        @(posedge CLK) disable iff (!RESETn) memToReg |-> regWrite
    );

    // regDst implies regWrite.
    check_regDst_implies_regWrite: assert property (
        @(posedge CLK) disable iff (!RESETn) regDst |-> regWrite
    );

    // memWrite implies not regWrite.
    check_memWrite_implies_no_regWrite: assert property (
        @(posedge CLK) disable iff (!RESETn) memWrite |-> !regWrite
    );

    // When op == 6'b000000, decode R-type controls.
    check_decode_op_000000: assert property (
        @(posedge CLK) disable iff (!RESETn)
            (op == 6'b000000) |-> (alu_op == 2'b10) && (regDst == 1'b1) && (regWrite == 1'b1) &&
                                 (memRead == 1'b0) && (memWrite == 1'b0) && (memToReg == 1'b0) &&
                                 (branch == 1'b0) && (aluSrc == 1'b0)
    );

    // When op == 6'b000100, decode branch controls.
    check_decode_op_000100: assert property (
        @(posedge CLK) disable iff (!RESETn)
            (op == 6'b000100) |-> (alu_op == 2'b01) && (branch == 1'b1) &&
                                 (memRead == 1'b0) && (memWrite == 1'b0) && (memToReg == 1'b0) &&
                                 (regDst == 1'b0) && (regWrite == 1'b0) && (aluSrc == 1'b0)
    );

    // When op == 6'b100011, decode load controls.
    check_decode_op_100011: assert property (
        @(posedge CLK) disable iff (!RESETn)
            (op == 6'b100011) |-> (memRead == 1'b1) && (memToReg == 1'b1) && (regWrite == 1'b1) &&
                                 (aluSrc == 1'b1) && (memWrite == 1'b0) && (branch == 1'b0) &&
                                 (regDst == 1'b0) && (alu_op == 2'b00)
    );

    // When op == 6'b101011, decode store controls.
    check_decode_op_101011: assert property (
        @(posedge CLK) disable iff (!RESETn)
            (op == 6'b101011) |-> (memWrite == 1'b1) && (aluSrc == 1'b1) &&
                                 (regWrite == 1'b0) && (memRead == 1'b0) && (memToReg == 1'b0) &&
                                 (branch == 1'b0) && (regDst == 1'b0) && (alu_op == 2'b00)
    );
endmodule