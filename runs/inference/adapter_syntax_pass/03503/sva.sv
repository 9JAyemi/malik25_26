module jt51_mod_sva (
    input logic m1_enters,
    input logic m2_enters,
    input logic c1_enters,
    input logic c2_enters,
    input logic [2:0] alg_I,
    input logic use_prevprev1,
    input logic use_internal_x,
    input logic use_internal_y,
    input logic use_prev2,
    input logic use_prev1
);

    // use_prevprev1 is m1 OR (m2 AND alg[5]).
    check_use_prevprev1_definition: assert property (
        @($global_clock)
        use_prevprev1 == (m1_enters | (m2_enters & (alg_I[5] == 1'b1)))
    );

    // use_prev2 is (m2 AND (alg[2:0] OR alg[3])) OR (c2 AND alg[3]).
    check_use_prev2_definition: assert property (
        @($global_clock)
        use_prev2 == ((m2_enters & ((|alg_I[2:0]) | (alg_I[3] == 1'b1))) |
                      (c2_enters & (alg_I[3] == 1'b1)))
    );

    // use_internal_x is c2 AND alg[2].
    check_use_internal_x_definition: assert property (
        @($global_clock)
        use_internal_x == (c2_enters & (alg_I[2] == 1'b1))
    );

    // use_internal_y is c2 AND (alg[4:3] OR alg[1:0]).
    check_use_internal_y_definition: assert property (
        @($global_clock)
        use_internal_y == (c2_enters & ((|alg_I[4:3]) | (|alg_I[1:0])))
    );

    // use_prev1 is m1 OR (m2 AND alg[1]) OR (c1 AND (alg[6:3] OR alg[0])) OR (c2 AND (alg[5] OR alg[2])).
    check_use_prev1_definition: assert property (
        @($global_clock)
        use_prev1 == (m1_enters |
                      (m2_enters & (alg_I[1] == 1'b1)) |
                      (c1_enters & ((|alg_I[6:3]) | (alg_I[0] == 1'b1))) |
                      (c2_enters & ((alg_I[5] == 1'b1) | (alg_I[2] == 1'b1))))
    );

    // use_prev1 includes the m1 path.
    check_use_prev1_includes_m1: assert property (
        @($global_clock)
        m1_enters |-> use_prev1
    );

    // use_prev1 includes the m2/alg[1] path.
    check_use_prev1_includes_m2_alg1: assert property (
        @($global_clock)
        (m2_enters & (alg_I[1] == 1'b1)) |-> use_prev1
    );

    // use_prev1 includes the c1/alg[6:3]/alg[0] path.
    check_use_prev1_includes_c1_path: assert property (
        @($global_clock)
        (c1_enters & ((|alg_I[6:3]) | (alg_I[0] == 1'b1))) |-> use_prev1
    );

    // use_prev1 includes the c2/alg[5]/alg[2] path.
    check_use_prev1_includes_c2_path: assert property (
        @($global_clock)
        (c2_enters & ((alg_I[5] == 1'b1) | (alg_I[2] == 1'b1))) |-> use_prev1
    );

    // use_prev1 is never low when all inputs are low.
    check_use_prev1_never_low_when_all_inputs_low: assert property (
        @($global_clock)
        (!m1_enters && !m2_enters && !c1_enters && !c2_enters && (alg_I == 3'd0)) |-> !use_prev1
    );

endmodule