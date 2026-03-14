module alu_32bit_sva (
    input logic CLK,
    input logic RESETn,        // Active-low reset for sampling; DUT has no reset
    input logic [31:0] A,
    input logic [31:0] B,
    input logic [2:0]  OPCODE,
    input logic        CIN,
    input logic        COUT,
    input logic [31:0] Y
);
    // DUT is purely combinational (no clock/reset); assertions are sampled on CLK.

    // Y matches add with carry-in when OPCODE==000.
    check_y_add: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (OPCODE == 3'b000) |-> (Y == (A + B + CIN))
    );

    // Y matches subtract with inverted borrow when OPCODE==001.
    check_y_sub: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (OPCODE == 3'b001) |-> (Y == (A - B - ~CIN))
    );

    // Y matches bitwise AND when OPCODE==010.
    check_y_and: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (OPCODE == 3'b010) |-> (Y == (A & B))
    );

    // Y matches bitwise OR when OPCODE==011.
    check_y_or: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (OPCODE == 3'b011) |-> (Y == (A | B))
    );

    // Y matches bitwise XOR when OPCODE==100.
    check_y_xor: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (OPCODE == 3'b100) |-> (Y == (A ^ B))
    );

    // Y matches logical shift-left by B when OPCODE==101.
    check_y_sll: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (OPCODE == 3'b101) |-> (Y == (A << B))
    );

    // Y matches logical shift-right by B when OPCODE==110.
    check_y_srl: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (OPCODE == 3'b110) |-> (Y == (A >> B))
    );

    // Y is zero in default case when OPCODE==111.
    check_y_default_zero: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (OPCODE == 3'b111) |-> (Y == 32'd0)
    );

    // COUT equation when OPCODE[1:0]==00.
    check_cout_for_op00: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (OPCODE[1:0] == 2'b00) |-> (COUT == ((Y[31] ^ CIN) & (OPCODE[2] ^ Y[30])))
    );

    // COUT equation when OPCODE[1:0]==01.
    check_cout_for_op01: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (OPCODE[1:0] == 2'b01) |-> (COUT == ((A[31] ^ B[31] ^ Y[31]) & (A[31] ^ CIN)))
    );

    // COUT is zero when OPCODE[1:0] is 10 or 11.
    check_cout_zero_for_op10_11: assert property (
        @(posedge CLK) disable iff (!RESETn)
        ((OPCODE[1:0] == 2'b10) || (OPCODE[1:0] == 2'b11)) |-> (COUT == 1'b0)
    );

endmodule