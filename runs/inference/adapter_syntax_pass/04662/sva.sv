module adder_8bit_sva (
    input logic [7:0] A,
    input logic [7:0] B,
    input logic       Cin,
    input logic [7:0] Sum,
    input logic       Cout
);

    // Sum and Cout must match the 9-bit addition of A, B, and Cin.
    check_full_add_result: assert property (
        @($global_clock)
        {Cout, Sum} == ({1'b0, A} + {1'b0, B} + {8'b0, Cin})
    );

    // Sum must equal the low 8 bits of the addition result.
    check_sum_matches_low_bits: assert property (
        @($global_clock)
        Sum == ({1'b0, A} + {1'b0, B} + {8'b0, Cin})[7:0]
    );

    // Cout must equal the carry-out of the addition.
    check_cout_matches_carry: assert property (
        @($global_clock)
        Cout == (({1'b0, A} + {1'b0, B} + {8'b0, Cin})[8] == 1'b1)
    );

    // Zero inputs must produce a zero result.
    check_zero_inputs_zero_result: assert property (
        @($global_clock)
        ((A == 8'h00) && (B == 8'h00) && (Cin == 1'b0)) |-> ((Sum == 8'h00) && (Cout == 1'b0))
    );

    // Adding zero with no carry-in must pass A through unchanged.
    check_a_passthrough_when_b_zero_and_cin_low: assert property (
        @($global_clock)
        ((B == 8'h00) && (Cin == 1'b0)) |-> ((Sum == A) && (Cout == 1'b0))
    );

    // Adding zero with no carry-in must pass B through unchanged.
    check_b_passthrough_when_a_zero_and_cin_low: assert property (
        @($global_clock)
        ((A == 8'h00) && (Cin == 1'b0)) |-> ((Sum == B) && (Cout == 1'b0))
    );

    // All-ones inputs with carry-in must produce the maximum 9-bit result.
    check_all_ones_maximum_result: assert property (
        @($global_clock)
        ((A == 8'hFF) && (B == 8'hFF) && (Cin == 1'b1)) |-> ((Sum == 8'hFF) && (Cout == 1'b1))
    );

endmodule