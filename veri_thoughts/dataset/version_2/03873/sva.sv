module four_bit_adder_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic Cin,
    input logic [3:0] S,
    input logic Cout
);

    // No explicit RTL clock or reset; sample on the formal global clock.

    // Full 5-bit result must equal A + B + Cin.
    check_total_sum: assert property (
        @($global_clock) {Cout, S} == ({1'b0, A} + {1'b0, B} + Cin)
    );

    // Cout must indicate when the 4-bit addition overflows.
    check_final_carry: assert property (
        @($global_clock) Cout == (({1'b0, A} + {1'b0, B} + Cin) >= 5'd16)
    );

    // Bit 0 sum must be the XOR of A[0], B[0], and Cin.
    check_lsb_sum: assert property (
        @($global_clock) S[0] == (A[0] ^ B[0] ^ Cin)
    );

    // Low 2 sum bits must match 2-bit addition.
    check_low_two_bits_sum: assert property (
        @($global_clock) {1'b0, S[1:0]} == ((({1'b0, A[1:0]} + {1'b0, B[1:0]} + Cin)) & 3'b011)
    );

    // Low 3 sum bits must match 3-bit addition.
    check_low_three_bits_sum: assert property (
        @($global_clock) {1'b0, S[2:0]} == ((({1'b0, A[2:0]} + {1'b0, B[2:0]} + Cin)) & 4'b0111)
    );

    // With A and B both zero, only Cin can affect the sum.
    check_cin_only: assert property (
        @($global_clock) (A == 4'b0000 && B == 4'b0000) |-> (S == {3'b000, Cin} && Cout == 1'b0)
    );

    // Adding zero on B with no carry-in must pass A through.
    check_add_zero_b: assert property (
        @($global_clock) (B == 4'b0000 && Cin == 1'b0) |-> (S == A && Cout == 1'b0)
    );

    // Adding zero on A with no carry-in must pass B through.
    check_add_zero_a: assert property (
        @($global_clock) (A == 4'b0000 && Cin == 1'b0) |-> (S == B && Cout == 1'b0)
    );

    // A plus bitwise complement of A with no carry-in must yield all ones.
    check_complement_no_carryin: assert property (
        @($global_clock) (B == ~A && Cin == 1'b0) |-> (S == 4'b1111 && Cout == 1'b0)
    );

    // A plus bitwise complement of A with carry-in must roll over with carry-out.
    check_complement_plus_one: assert property (
        @($global_clock) (B == ~A && Cin == 1'b1) |-> (S == 4'b0000 && Cout == 1'b1)
    );

endmodule