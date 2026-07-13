module sky130_fd_sc_ls__a2bb2oi_sva (
    input logic Y,
    input logic A1_N,
    input logic A2_N,
    input logic B1,
    input logic B2
);

    // Y matches the implemented gate equation.
    check_output_equation: assert property (
        @($global_clock) Y == ~((~(A1_N | A2_N)) | (B1 & B2))
    );

    // Both B inputs high force the output low.
    check_b_and_forces_low: assert property (
        @($global_clock) (B1 && B2) |-> !Y
    );

    // Both A inputs low force the output low.
    check_a_inputs_low_force_low: assert property (
        @($global_clock) (!A1_N && !A2_N) |-> !Y
    );

    // A1_N can drive Y high when the B path is inactive.
    check_a1_path_drives_high: assert property (
        @($global_clock) (A1_N && !(B1 && B2)) |-> Y
    );

    // A2_N can drive Y high when the B path is inactive.
    check_a2_path_drives_high: assert property (
        @($global_clock) (A2_N && !(B1 && B2)) |-> Y
    );

    // A high output requires at least one A input high.
    check_high_output_requires_a_path: assert property (
        @($global_clock) Y |-> (A1_N || A2_N)
    );

    // A high output requires the B AND term to be low.
    check_high_output_blocks_b_and: assert property (
        @($global_clock) Y |-> !(B1 && B2)
    );

    // A low output with an asserted A path must come from B1&B2 being high.
    check_low_output_with_a_path_requires_b_and: assert property (
        @($global_clock) (!Y && (A1_N || A2_N)) |-> (B1 && B2)
    );

    // A low output without the B AND term must come from both A inputs being low.
    check_low_output_without_b_and_requires_a_low: assert property (
        @($global_clock) (!Y && !(B1 && B2)) |-> (!A1_N && !A2_N)
    );

endmodule