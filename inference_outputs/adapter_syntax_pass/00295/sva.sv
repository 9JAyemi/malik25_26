module top_module_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [2:0] opcode,
    input logic [3:0] out,
    input logic zero
);

    // No RTL clock or reset; sample combinational behavior on the formal global clock.

    // opcode 000 selects addition.
    check_add_result: assert property (
        @($global_clock) (opcode == 3'b000) |-> (out == (A + B))
    );

    // opcode 001 selects subtraction.
    check_sub_result: assert property (
        @($global_clock) (opcode == 3'b001) |-> (out == (A - B))
    );

    // opcode 010 selects bitwise AND.
    check_and_result: assert property (
        @($global_clock) (opcode == 3'b010) |-> (out == (A & B))
    );

    // opcode 011 selects bitwise OR.
    check_or_result: assert property (
        @($global_clock) (opcode == 3'b011) |-> (out == (A | B))
    );

    // opcode 100 selects bitwise XOR.
    check_xor_result: assert property (
        @($global_clock) (opcode == 3'b100) |-> (out == (A ^ B))
    );

    // Any non-zero opcode selects the default zero result.
    check_default_zero_result: assert property (
        @($global_clock) (opcode != 3'b000 && opcode != 3'b001 && opcode != 3'b010 && opcode != 3'b011 && opcode != 3'b100) |-> (out == 4'h0)
    );

    // Zero output implies the zero flag is asserted.
    check_zero_flag_when_out_zero: assert property (
        @($global_clock) (out == 4'h0) |-> (zero == 1'b1)
    );

    // Nonzero output implies the zero flag is deasserted.
    check_zero_flag_when_out_nonzero: assert property (
        @($global_clock) (out != 4'h0) |-> (zero == 1'b0)
    );

    // The top-level output is the OR of the ALU result and the constant 4'hF.
    check_top_level_or_result: assert property (
        @($global_clock) out == ((A | B) | 4'hF)
    );

endmodule