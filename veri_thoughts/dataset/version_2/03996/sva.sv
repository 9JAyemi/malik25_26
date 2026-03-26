module four_bit_adder_sva (
    input logic        clk,
    input logic [3:0]  A,
    input logic [3:0]  B,
    input logic        Cin,
    input logic [3:0]  S,
    input logic        Cout
);

    // External clk samples a combinational DUT; the RTL has no reset.

    // The concatenated carry and sum match 5-bit unsigned addition.
    check_total_sum: assert property (
        @(posedge clk) ({Cout, S} == ({1'b0, A} + {1'b0, B} + {4'b0000, Cin}))
    );

    // The least-significant sum bit follows the first full-adder XOR equation.
    check_lsb_sum: assert property (
        @(posedge clk) (S[0] == (A[0] ^ B[0] ^ Cin))
    );

    // The sum bus matches the low four bits of the arithmetic result.
    check_sum_bus: assert property (
        @(posedge clk) (S == (({1'b0, A} + {1'b0, B} + {4'b0000, Cin})[3:0]))
    );

    // Cout matches the carry-out bit of the arithmetic result.
    check_carry_out: assert property (
        @(posedge clk) (Cout == (({1'b0, A} + {1'b0, B} + {4'b0000, Cin})[4]))
    );

    // Adding zero with no carry-in passes A through unchanged.
    check_add_zero_passes_a: assert property (
        @(posedge clk) (((B == 4'b0000) && (Cin == 1'b0)) |-> ((S == A) && (Cout == 1'b0)))
    );

    // Adding zero with no carry-in passes B through unchanged.
    check_add_zero_passes_b: assert property (
        @(posedge clk) (((A == 4'b0000) && (Cin == 1'b0)) |-> ((S == B) && (Cout == 1'b0)))
    );

endmodule