module NAND4AND2_sva (
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic [1:0] Z
);

    // Z[0] is the OR of the two input AND terms.
    check_z0_function: assert property (
        @($global_clock) Z[0] == ((A & B) | (C & D))
    );

    // Z[1] is the inverse of the two input AND terms OR.
    check_z1_function: assert property (
        @($global_clock) Z[1] == ~((A & B) | (C & D))
    );

    // The two output bits are always complementary.
    check_outputs_complementary: assert property (
        @($global_clock) Z[1] == ~Z[0]
    );

    // A and B high force the true output encoding.
    check_ab_pair_sets_true_output: assert property (
        @($global_clock) (A & B) |-> ((Z[0] == 1'b1) && (Z[1] == 1'b0))
    );

    // C and D high force the true output encoding.
    check_cd_pair_sets_true_output: assert property (
        @($global_clock) (C & D) |-> ((Z[0] == 1'b1) && (Z[1] == 1'b0))
    );

    // No high input pair forces the false output encoding.
    check_no_pair_sets_false_output: assert property (
        @($global_clock) !((A & B) | (C & D)) |-> ((Z[0] == 1'b0) && (Z[1] == 1'b1))
    );

endmodule