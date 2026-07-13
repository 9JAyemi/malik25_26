module AND4_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] Z
);

    // Z must always match the implemented AND function.
    check_and4_function: assert property (
        @($global_clock) (Z == ~(~A | ~B))
    );

    // A zero vector must force Z low.
    check_zero_output_when_a_zero: assert property (
        @($global_clock) (A == 4'b0000) |-> (Z == 4'b0000)
    );

    // B zero vector must force Z low.
    check_zero_output_when_b_zero: assert property (
        @($global_clock) (B == 4'b0000) |-> (Z == 4'b0000)
    );

    // All ones on A must pass B through to Z.
    check_pass_b_when_a_all_ones: assert property (
        @($global_clock) (A == 4'b1111) |-> (Z == B)
    );

    // All ones on B must pass A through to Z.
    check_pass_a_when_b_all_ones: assert property (
        @($global_clock) (B == 4'b1111) |-> (Z == A)
    );

endmodule