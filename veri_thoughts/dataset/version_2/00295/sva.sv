module top_module_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [2:0] opcode,
    input logic [3:0] out,
    input logic zero
);

    // Out is always all ones because the ALU result is ORed with 4'hF.
    check_out_forced_ones: assert property (
        @($global_clock) out == 4'hF
    );

    // Add opcode makes zero reflect a zero 4-bit sum.
    check_zero_on_add: assert property (
        @($global_clock) (opcode == 3'b000) |-> (zero == ((((A + B) & 4'hF) == 4'h0)))
    );

    // Subtract opcode makes zero reflect a zero 4-bit difference.
    check_zero_on_sub: assert property (
        @($global_clock) (opcode == 3'b001) |-> (zero == ((((A - B) & 4'hF) == 4'h0)))
    );

    // AND opcode makes zero reflect an all-zero bitwise AND result.
    check_zero_on_and: assert property (
        @($global_clock) (opcode == 3'b010) |-> (zero == ((A & B) == 4'h0))
    );

    // OR opcode makes zero reflect an all-zero bitwise OR result.
    check_zero_on_or: assert property (
        @($global_clock) (opcode == 3'b011) |-> (zero == ((A | B) == 4'h0))
    );

    // XOR opcode makes zero reflect an all-zero bitwise XOR result.
    check_zero_on_xor: assert property (
        @($global_clock) (opcode == 3'b100) |-> (zero == ((A ^ B) == 4'h0))
    );

    // Default opcodes drive a zero ALU result, so zero must be high.
    check_zero_on_default: assert property (
        @($global_clock) ((opcode == 3'b101) || (opcode == 3'b110) || (opcode == 3'b111)) |-> (zero == 1'b1)
    );

endmodule