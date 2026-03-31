module alu_sva (
    input logic CLK,
    input logic RESETn,
    input logic [31:0] a,
    input logic [31:0] b,
    input logic [4:0]  aluc,
    input logic [31:0] result
);
    // Addition (signed) opcode 0: result = a + b
    check_add_signed: assert property (
        @(posedge CLK) disable iff (!RESETn) (aluc == 5'd0) |-> (result == (a + b))
    );

    // Addition (unsigned) opcode 1: result = a + b
    check_add_unsigned: assert property (
        @(posedge CLK) disable iff (!RESETn) (aluc == 5'd1) |-> (result == (a + b))
    );

    // Subtraction (signed) opcode 2: result = a - b
    check_sub_signed: assert property (
        @(posedge CLK) disable iff (!RESETn) (aluc == 5'd2) |-> (result == (a - b))
    );

    // Subtraction (unsigned) opcode 3: result = a - b
    check_sub_unsigned: assert property (
        @(posedge CLK) disable iff (!RESETn) (aluc == 5'd3) |-> (result == (a - b))
    );

    // Bitwise AND opcode 4: result = a & b
    check_and: assert property (
        @(posedge CLK) disable iff (!RESETn) (aluc == 5'd4) |-> (result == (a & b))
    );

    // Bitwise OR opcode 5: result = a | b
    check_or: assert property (
        @(posedge CLK) disable iff (!RESETn) (aluc == 5'd5) |-> (result == (a | b))
    );

    // Bitwise XOR opcode 6: result = a ^ b
    check_xor: assert property (
        @(posedge CLK) disable iff (!RESETn) (aluc == 5'd6) |-> (result == (a ^ b))
    );

    // Bitwise NOR opcode 7: result = ~(a | b)
    check_nor: assert property (
        @(posedge CLK) disable iff (!RESETn) (aluc == 5'd7) |-> (result == ~(a | b))
    );

    // Set Less Than (signed) opcode 8: result = 1 or 0 per signed comparison
    check_slt_signed: assert property (
        @(posedge CLK) disable iff (!RESETn)
            (aluc == 5'd8) |-> (result == ((a[31]^b[31]) ? (a[31] ? 32'd1 : 32'd0) : ((a < b) ? 32'd1 : 32'd0)))
    );

    // Set Less Than (unsigned) opcode 9: result = 1 or 0 per unsigned comparison
    check_slt_unsigned: assert property (
        @(posedge CLK) disable iff (!RESETn)
            (aluc == 5'd9) |-> (result == ((a < b) ? 32'd1 : 32'd0))
    );

    // Shift Left Logical opcode 10: result = b << a
    check_sll: assert property (
        @(posedge CLK) disable iff (!RESETn) (aluc == 5'd10) |-> (result == (b << a))
    );

    // Shift Right Logical opcode 11: result = b >> a
    check_srl: assert property (
        @(posedge CLK) disable iff (!RESETn) (aluc == 5'd11) |-> (result == (b >> a))
    );

    // Shift Right Arithmetic opcode 12: result = $signed(b) >>> a
    check_sra: assert property (
        @(posedge CLK) disable iff (!RESETn) (aluc == 5'd12) |-> (result == ($signed(b) >>> a))
    );

    // Load Upper Immediate opcode 14: result = {b[15:0], 16'b0}
    check_lui: assert property (
        @(posedge CLK) disable iff (!RESETn) (aluc == 5'd14) |-> (result == {b[15:0], 16'b0})
    );

    // Zero opcode 31: result = 0
    check_zero_opcode: assert property (
        @(posedge CLK) disable iff (!RESETn) (aluc == 5'd31) |-> (result == 32'd0)
    );

    // Default/invalid opcode: result = 0
    check_default_zero: assert property (
        @(posedge CLK) disable iff (!RESETn)
            (!(aluc inside {5'd0,5'd1,5'd2,5'd3,5'd4,5'd5,5'd6,5'd7,5'd8,5'd9,5'd10,5'd11,5'd12,5'd14,5'd31})) |-> (result == 32'd0)
    );

    // Shift-by-zero identity for SLL: a==0 leaves b unchanged
    check_sll_shift0_identity: assert property (
        @(posedge CLK) disable iff (!RESETn) (aluc == 5'd10 && a == 32'd0) |-> (result == b)
    );

    // Shift-by-zero identity for SRL: a==0 leaves b unchanged
    check_srl_shift0_identity: assert property (
        @(posedge CLK) disable iff (!RESETn) (aluc == 5'd11 && a == 32'd0) |-> (result == b)
    );

    // Shift-by-zero identity for SRA: a==0 leaves b unchanged
    check_sra_shift0_identity: assert property (
        @(posedge CLK) disable iff (!RESETn) (aluc == 5'd12 && a == 32'd0) |-> (result == b)
    );

    // SRL with nonzero shift inserts 0 at MSB
    check_srl_msb_zero_on_shift: assert property (
        @(posedge CLK) disable iff (!RESETn) (aluc == 5'd11 && a != 32'd0) |-> (result[31] == 1'b0)
    );

    // SRA with nonzero shift preserves sign bit at MSB
    check_sra_msb_sign_extend: assert property (
        @(posedge CLK) disable iff (!RESETn) (aluc == 5'd12 && a != 32'd0) |-> (result[31] == b[31])
    );

    // LUI guarantees lower 16 bits are zero
    check_lui_low16_zero: assert property (
        @(posedge CLK) disable iff (!RESETn) (aluc == 5'd14) |-> (result[15:0] == 16'b0)
    );
endmodule