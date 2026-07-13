module four_bit_adder_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic       Cin,
    input logic [3:0] Sum,
    input logic       Cout
);

    // No RTL clock or reset; sample this combinational logic on Jasper's global clock.

    // Combined carry and sum must equal the 5-bit addition of A, B, and Cin.
    check_combined_addition: assert property (
        @($global_clock) {Cout, Sum} == ({1'b0, A} + {1'b0, B} + Cin)
    );

    // The least-significant sum bit must match the LSB full-adder equation.
    check_lsb_sum: assert property (
        @($global_clock) Sum[0] == (A[0] ^ B[0] ^ Cin)
    );

    // Zero operands with no carry-in must produce a zero result.
    check_zero_result: assert property (
        @($global_clock) ((A == 4'b0000) && (B == 4'b0000) && (Cin == 1'b0)) |-> ((Sum == 4'b0000) && (Cout == 1'b0))
    );

    // Carry-out must be asserted exactly when the 5-bit total is 16 or more.
    check_carry_threshold: assert property (
        @($global_clock) Cout == (({1'b0, A} + {1'b0, B} + Cin) >= 5'd16)
    );

endmodule