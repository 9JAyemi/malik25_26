module fourBitAdder_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic       Cin,
    input logic [3:0] Sum,
    input logic       Cout
);

    // Sum and Cout must match the 5-bit addition of A, B, and Cin.
    check_full_add_result: assert property (
        @($global_clock)
        {Cout, Sum} == ({1'b0, A} + {1'b0, B} + {4'b0000, Cin})
    );

    // Sum must be the low 4 bits of the addition result.
    check_sum_low_bits: assert property (
        @($global_clock)
        Sum == (A + B + Cin)
    );

    // Cout must be high exactly when the addition overflows 4 bits.
    check_cout_overflow: assert property (
        @($global_clock)
        Cout == (({1'b0, A} + {1'b0, B} + {4'b0000, Cin}) >= 5'd16)
    );

    // Zero inputs must produce a zero result.
    check_zero_inputs: assert property (
        @($global_clock)
        ((A == 4'd0) && (B == 4'd0) && (Cin == 1'b0)) |-> ((Sum == 4'd0) && (Cout == 1'b0))
    );

    // Adding zero with no carry-in must pass A through unchanged.
    check_pass_a_when_b_zero: assert property (
        @($global_clock)
        ((B == 4'd0) && (Cin == 1'b0)) |-> ((Sum == A) && (Cout == 1'b0))
    );

    // Adding zero with no carry-in must pass B through unchanged.
    check_pass_b_when_a_zero: assert property (
        @($global_clock)
        ((A == 4'd0) && (Cin == 1'b0)) |-> ((Sum == B) && (Cout == 1'b0))
    );

    // All ones plus carry-in must produce the maximum 5-bit result.
    check_max_addition_case: assert property (
        @($global_clock)
        ((A == 4'hF) && (B == 4'hF) && (Cin == 1'b1)) |-> ((Sum == 4'hF) && (Cout == 1'b1))
    );

endmodule