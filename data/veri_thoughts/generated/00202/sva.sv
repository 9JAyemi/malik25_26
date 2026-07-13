module alu_assertions (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [2:0] opcode,
    input logic carry_in,
    input logic invert,
    input logic [3:0] result,
    input logic carry_out
);

    // Addition result is the 4-bit sum, optionally inverted.
    check_add_result: assert property (
        @(posedge clk)
        (opcode == 3'b000) |-> (result == (invert ? ~(A + B + carry_in) : (A + B + carry_in)))
    );

    // Subtraction result is the 4-bit difference, optionally inverted.
    check_subtract_result: assert property (
        @(posedge clk)
        (opcode == 3'b001) |-> (result == (invert ? ~(A - B - carry_in) : (A - B - carry_in)))
    );

    // AND opcode drives bitwise AND, optionally inverted.
    check_and_result: assert property (
        @(posedge clk)
        (opcode == 3'b010) |-> (result == (invert ? ~(A & B) : (A & B)))
    );

    // OR opcode drives bitwise OR, optionally inverted.
    check_or_result: assert property (
        @(posedge clk)
        (opcode == 3'b011) |-> (result == (invert ? ~(A | B) : (A | B)))
    );

    // XOR opcode drives bitwise XOR, optionally inverted.
    check_xor_result: assert property (
        @(posedge clk)
        (opcode == 3'b100) |-> (result == (invert ? ~(A ^ B) : (A ^ B)))
    );

    // Unsupported opcodes drive zero, optionally inverted to all ones.
    check_default_result: assert property (
        @(posedge clk)
        ((opcode == 3'b101) || (opcode == 3'b110) || (opcode == 3'b111))
        |-> (result == (invert ? 4'hF : 4'h0))
    );

    // Addition carry_out matches the RTL carry formula.
    check_add_carry_out: assert property (
        @(posedge clk)
        (opcode == 3'b000)
        |-> (carry_out == ((A[3] & B[3]) | (A[3] & carry_in) | (B[3] & carry_in)))
    );

    // Subtraction carry_out matches the RTL subtraction formula.
    check_subtract_carry_out: assert property (
        @(posedge clk)
        (opcode == 3'b001)
        |-> (carry_out == ((A[3] & ~B[3] & ~carry_in) | (~A[3] & B[3] & carry_in)))
    );

    // Logical opcodes force carry_out low.
    check_logical_carry_out_low: assert property (
        @(posedge clk)
        ((opcode == 3'b010) || (opcode == 3'b011) || (opcode == 3'b100))
        |-> (carry_out == 1'b0)
    );

    // Unsupported opcodes also force carry_out low.
    check_default_carry_out_low: assert property (
        @(posedge clk)
        ((opcode == 3'b101) || (opcode == 3'b110) || (opcode == 3'b111))
        |-> (carry_out == 1'b0)
    );

endmodule