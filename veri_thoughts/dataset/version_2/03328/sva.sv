module alu8b_sva (
    input logic [7:0] A_in,
    input logic [7:0] B_in,
    input logic       C_in,
    input logic [2:0] Opcode_in,
    input logic [7:0] Result_out,
    input logic       C_out
);

    // Add opcode returns the 9-bit sum across carry and result.
    check_add_operation: assert property (
        @($global_clock)
        (Opcode_in == 3'b000) |-> ({C_out, Result_out} == ({1'b0, A_in} + {1'b0, B_in} + {{8{1'b0}}, C_in}))
    );

    // Subtract opcode returns A minus B in the result.
    check_sub_operation: assert property (
        @($global_clock)
        (Opcode_in == 3'b001) |-> (Result_out == (A_in - B_in))
    );

    // AND opcode returns the bitwise AND of the inputs.
    check_and_operation: assert property (
        @($global_clock)
        (Opcode_in == 3'b010) |-> (Result_out == (A_in & B_in))
    );

    // OR opcode returns the bitwise OR of the inputs.
    check_or_operation: assert property (
        @($global_clock)
        (Opcode_in == 3'b011) |-> (Result_out == (A_in | B_in))
    );

    // Modulo opcode returns A modulo B when the divisor is nonzero.
    check_mod_operation: assert property (
        @($global_clock)
        ((Opcode_in == 3'b100) && (B_in != 8'b0)) |-> (Result_out == (A_in % B_in))
    );

    // Unimplemented opcodes drive a zero result and zero carry.
    check_default_zero_outputs: assert property (
        @($global_clock)
        ((Opcode_in == 3'b101) || (Opcode_in == 3'b110) || (Opcode_in == 3'b111)) |-> ((Result_out == 8'b0) && (C_out == 1'b0))
    );

    // All non-add operations force the carry output low.
    check_non_add_carry_zero: assert property (
        @($global_clock)
        (Opcode_in != 3'b000) |-> (C_out == 1'b0)
    );

endmodule