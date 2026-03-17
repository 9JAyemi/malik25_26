module four_bit_adder_assertions (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic Cin,
    input logic [3:0] S,
    input logic Cout
);

    // Output vector equals A plus B plus carry-in.
    check_total_sum: assert property (
        @(posedge clk) {Cout, S} == ({1'b0, A} + {1'b0, B} + Cin)
    );

    // Least significant sum bit matches the first full adder.
    check_lsb_sum: assert property (
        @(posedge clk) S[0] == (A[0] ^ B[0] ^ Cin)
    );

    // Bit 1 sum uses the carry from bit 0.
    check_bit1_sum: assert property (
        @(posedge clk) S[1] == (A[1] ^ B[1] ^ (({1'b0, A[0]} + {1'b0, B[0]} + Cin) >= 2'd2))
    );

    // Bit 2 sum uses the carry from bits [1:0].
    check_bit2_sum: assert property (
        @(posedge clk) S[2] == (A[2] ^ B[2] ^ (({1'b0, A[1:0]} + {1'b0, B[1:0]} + Cin) >= 3'd4))
    );

    // Bit 3 sum uses the carry from bits [2:0].
    check_msb_sum: assert property (
        @(posedge clk) S[3] == (A[3] ^ B[3] ^ (({1'b0, A[2:0]} + {1'b0, B[2:0]} + Cin) >= 4'd8))
    );

    // Carry out is high exactly when the 4-bit addition overflows.
    check_cout_overflow: assert property (
        @(posedge clk) Cout == (({1'b0, A} + {1'b0, B} + Cin) >= 5'd16)
    );

    // Adding zero on B with no carry-in passes A through.
    check_add_zero_b: assert property (
        @(posedge clk) ((B == 4'b0000) && (Cin == 1'b0)) |-> ({Cout, S} == {1'b0, A})
    );

    // Adding zero on A with no carry-in passes B through.
    check_add_zero_a: assert property (
        @(posedge clk) ((A == 4'b0000) && (Cin == 1'b0)) |-> ({Cout, S} == {1'b0, B})
    );

endmodule