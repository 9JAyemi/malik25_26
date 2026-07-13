module jt51_mod_sva (
    input logic       m1_enters,
    input logic       m2_enters,
    input logic       c1_enters,
    input logic       c2_enters,
    input logic [2:0] alg_I,
    input logic       use_prevprev1,
    input logic       use_internal_x,
    input logic       use_internal_y,
    input logic       use_prev2,
    input logic       use_prev1
);

    // use_prevprev1 matches the RTL case mapping and m2_enters gating.
    check_use_prevprev1_definition: assert property (
        @($global_clock)
        use_prevprev1 == ((m1_enters) |
                          ((m2_enters) & ((alg_I == 3'd0) | (alg_I == 3'd1) | (alg_I == 3'd2) | (alg_I == 3'd3))))
    );

    // use_prev2 matches the RTL m2_enters gating and c2_enters path.
    check_use_prev2_definition: assert property (
        @($global_clock)
        use_prev2 == (((m2_enters) & ((alg_I == 3'd0) | (alg_I == 3'd1) | (alg_I == 3'd2) | (alg_I == 3'd3))) |
                      ((c2_enters) & ((alg_I == 3'd4) | (alg_I == 3'd5) | (alg_I == 3'd6) | (alg_I == 3'd7))))
    );

    // use_internal_x matches the RTL c2_enters gating and alg_I[2] decode.
    check_use_internal_x_definition: assert property (
        @($global_clock)
        use_internal_x == ((c2_enters) & ((alg_I == 3'd4) | (alg_I == 3'd5) | (alg_I == 3'd6) | (alg_I == 3'd7)))
    );

    // use_internal_y matches the RTL c2_enters gating and alg_I[4:3]/[1:0] decode.
    check_use_internal_y_definition: assert property (
        @($global_clock)
        use_internal_y == ((c2_enters) & ((alg_I == 3'd6) | (alg_I == 3'd7)))
    );

    // use_prev1 matches the RTL m1_enters gating and all c1/c2 gating terms.
    check_use_prev1_definition: assert property (
        @($global_clock)
        use_prev1 == ((m1_enters) |
                      ((m2_enters) & ((alg_I == 3'd0) | (alg_I == 3'd1) | (alg_I == 3'd2) | (alg_I == 3'd3))) |
                      ((c1_enters) & ((alg_I == 3'd0) | (alg_I == 3'd1) | (alg_I == 3'd2) | (alg_I == 3'd3))) |
                      ((c2_enters) & ((alg_I == 3'd4) | (alg_I == 3'd5) | (alg_I == 3'd6) | (alg_I == 3'd7))))
    );

    // use_internal_y implies use_internal_x.
    check_use_internal_y_implies_use_internal_x: assert property (
        @($global_clock)
        use_internal_y |-> use_internal_x
    );

    // use_internal_x and use_internal_y are never asserted together.
    check_use_internal_xy_mutex: assert property (
        @($global_clock)
        !(use_internal_x && use_internal_y)
    );

    // use_prev2 implies use_prevprev1.
    check_use_prev2_implies_use_prevprev1: assert property (
        @($global_clock)
        use_prev2 |-> use_prevprev1
    );

    // use_prev1 implies use_prevprev1.
    check_use_prev1_implies_use_prevprev1: assert property (
        @($global_clock)
        use_prev1 |-> use_prevprev1
    );

    // use_prev1 implies use_prev2.
    check_use_prev1_implies_use_prev2: assert property (
        @($global_clock)
        use_prev1 |-> use_prev2
    );

endmodule