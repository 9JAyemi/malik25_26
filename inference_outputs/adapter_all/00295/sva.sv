module top_module_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [2:0] opcode,
    input logic [3:0] out,
    input logic zero
);

    // No RTL clock or reset; sample combinational behavior on the global clock.

    // Opcode 000 selects addition and drives zero low.
    check_add_result: assert property (
        @($global_clock)
        (opcode == 3'b000) |-> ((out == (A + B)) && (zero == 1'b0))
    );

    // Opcode 001 selects subtraction and drives zero low.
    check_sub_result: assert property (
        @($global_clock)
        (opcode == 3'b001) |-> ((out == (A - B)) && (zero == 1'b0))
    );

    // Opcode 010 selects bitwise AND and drives zero low.
    check_and_result: assert property (
        @($global_clock)
        (opcode == 3'b010) |-> ((out == (A & B)) && (zero == 1'b0))
    );

    // Opcode 011 selects bitwise OR and drives zero low.
    check_or_result: assert property (
        @($global_clock)
        (opcode == 3'b011) |-> ((out == (A | B)) && (zero == 1'b0))
    );

    // Opcode 100 selects bitwise XOR and drives zero low.
    check_xor_result: assert property (
        @($global_clock)
        (opcode == 3'b100) |-> ((out == (A ^ B)) && (zero == 1'b0))
    );

    // Any unimplemented opcode drives zero high.
    check_default_zero: assert property (
        @($global_clock)
        (opcode inside {3'b101, 3'b110, 3'b111}) |-> (zero == 1'b1)
    );

    // Zero output only occurs for the default opcode and zero inputs.
    check_zero_output_only_for_default_zero: assert property (
        @($global_clock)
        (zero == 1'b1) |-> ((opcode inside {3'b101, 3'b110, 3'b111}) && (A == 4'b0000) && (B == 4'b0000))
    );

endmodule