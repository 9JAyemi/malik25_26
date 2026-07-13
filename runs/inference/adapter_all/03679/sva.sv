module fourBitAdder_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic Cin,
    input logic [3:0] Sum,
    input logic Cout
);

    // Sum and Cout together equal the 5-bit addition of A, B, and Cin.
    check_full_add_result: assert property (
        @($global_clock) {Cout, Sum} == ({1'b0, A} + {1'b0, B} + Cin)
    );

    // Sum matches the low 4 bits of the 5-bit addition.
    check_sum_low_bits: assert property (
        @($global_clock) Sum == (({1'b0, A} + {1'b0, B} + Cin)[3:0])
    );

    // Cout matches the carry-out bit of the 5-bit addition.
    check_cout_carry: assert property (
        @($global_clock) Cout == (({1'b0, A} + {1'b0, B} + Cin)[4])
    );

    // Adding zero on B with Cin low passes A through unchanged.
    check_add_zero_b: assert property (
        @($global_clock) (B == 4'h0 && Cin == 1'b0) |-> (Sum == A && Cout == 1'b0)
    );

    // Adding zero on A with Cin low passes B through unchanged.
    check_add_zero_a: assert property (
        @($global_clock) (A == 4'h0 && Cin == 1'b0) |-> (Sum == B && Cout == 1'b0)
    );

    // With A and B zero, Cout follows Cin and Sum is zero.
    check_zero_inputs: assert property (
        @($global_clock) (A == 4'h0 && B == 4'h0) |-> (Sum == 4'h0 && Cout == Cin)
    );

    // With A and B equal to 4'hF, Cout is high regardless of Cin.
    check_max_plus_max: assert property (
        @($global_clock) (A == 4'hF && B == 4'hF) |-> (Cout == 1'b1 && Sum == 4'hE)
    );

    // With A equal to 4'hF and B equal to 4'h1, Cout follows Cin and Sum is zero.
    check_max_plus_one: assert property (
        @($global_clock) (A == 4'hF && B == 4'h1) |-> (Cout == Cin && Sum == 4'h0)
    );

    // With A equal to 4'h1 and B equal to 4'hF, Cout follows Cin and Sum is zero.
    check_one_plus_max: assert property (
        @($global_clock) (A == 4'h1 && B == 4'hF) |-> (Cout == Cin && Sum == 4'h0)
    );

    // With A equal to 4'h8 and B equal to 4'h8, Cout is high regardless of Cin.
    check_eight_plus_eight: assert property (
        @($global_clock) (A == 4'h8 && B == 4'h8) |-> (Cout == 1'b1 && Sum == 4'h0)
    );

endmodule