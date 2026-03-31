module adder_8bit_sva (
    input logic [7:0] A,
    input logic [7:0] B,
    input logic       Cin,
    input logic [7:0] Sum,
    input logic       Cout
);

    // Sum and Cout must equal the 9-bit addition of A, B, and Cin.
    check_full_add_result: assert property (
        @($global_clock) {Cout, Sum} == ({1'b0, A} + {1'b0, B} + Cin)
    );

    // Sum must match the low 8 bits of the addition result.
    check_sum_low_bits: assert property (
        @($global_clock) Sum == (({1'b0, A} + {1'b0, B} + Cin)[7:0])
    );

    // Cout must match the carry-out bit of the addition result.
    check_cout_carry_bit: assert property (
        @($global_clock) Cout == (({1'b0, A} + {1'b0, B} + Cin)[8])
    );

    // Adding zero on B with Cin low must pass A through unchanged.
    check_add_zero_b: assert property (
        @($global_clock) (B == 8'h00 && Cin == 1'b0) |-> (Sum == A && Cout == 1'b0)
    );

    // Adding zero on A with Cin low must pass B through unchanged.
    check_add_zero_a: assert property (
        @($global_clock) (A == 8'h00 && Cin == 1'b0) |-> (Sum == B && Cout == 1'b0)
    );

    // With A and B low, Cin must increment the zero result by one.
    check_cin_only: assert property (
        @($global_clock) (A == 8'h00 && B == 8'h00) |-> (Sum == 8'h01 && Cout == 1'b0)
    );

    // With A and B high, Cin must increment the all-ones result by one.
    check_all_ones_plus_cin: assert property (
        @($global_clock) (A == 8'hFF && B == 8'hFF) |-> (Sum == 8'h00 && Cout == 1'b1)
    );

    // Adding 8'hFF and 8'h01 with Cin low must wrap the sum and raise carry.
    check_ff_plus_one: assert property (
        @($global_clock) (A == 8'hFF && B == 8'h01 && Cin == 1'b0) |-> (Sum == 8'h00 && Cout == 1'b1)
    );

    // Adding 8'hFF and 8'h01 with Cin high must wrap the sum and raise carry.
    check_ff_plus_one_with_cin: assert property (
        @($global_clock) (A == 8'hFF && B == 8'h01 && Cin == 1'b1) |-> (Sum == 8'h01 && Cout == 1'b1)
    );

    // Adding 8'h80 and 8'h80 with Cin low must produce 8'h00 with carry.
    check_80_plus_80: assert property (
        @($global_clock) (A == 8'h80 && B == 8'h80 && Cin == 1'b0) |-> (Sum == 8'h00 && Cout == 1'b1)
    );

endmodule