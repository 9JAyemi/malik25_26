module jt51_mod_sva (
    input logic       clk,
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

    // Combinational DUT sampled on an external clock; there is no RTL reset.

    // use_prevprev1 matches the m1 or m2/alg5 decode.
    check_use_prevprev1_decode: assert property (
        @(posedge clk)
        use_prevprev1 == (m1_enters | (m2_enters & (alg_I == 3'd5)))
    );

    // use_prev2 matches the m2/alg0-2 or c2/alg3 decode.
    check_use_prev2_decode: assert property (
        @(posedge clk)
        use_prev2 == (
            (m2_enters & ((alg_I == 3'd0) | (alg_I == 3'd1) | (alg_I == 3'd2))) |
            (c2_enters & (alg_I == 3'd3))
        )
    );

    // use_internal_x matches the c2/alg2 decode.
    check_use_internal_x_decode: assert property (
        @(posedge clk)
        use_internal_x == (c2_enters & (alg_I == 3'd2))
    );

    // use_internal_y matches the c2/alg0,1,3,4 decode.
    check_use_internal_y_decode: assert property (
        @(posedge clk)
        use_internal_y == (
            c2_enters &
            ((alg_I == 3'd0) | (alg_I == 3'd1) | (alg_I == 3'd3) | (alg_I == 3'd4))
        )
    );

    // use_prev1 matches the combined m1, m2, c1, and c2 decode.
    check_use_prev1_decode: assert property (
        @(posedge clk)
        use_prev1 == (
            m1_enters |
            (m2_enters & (alg_I == 3'd1)) |
            (c1_enters & (
                (alg_I == 3'd0) | (alg_I == 3'd3) | (alg_I == 3'd4) |
                (alg_I == 3'd5) | (alg_I == 3'd6)
            )) |
            (c2_enters & ((alg_I == 3'd2) | (alg_I == 3'd5)))
        )
    );

    // With no enter inputs asserted, all outputs are low.
    check_no_enters_clear_outputs: assert property (
        @(posedge clk)
        (!m1_enters && !m2_enters && !c1_enters && !c2_enters) |->
        (!use_prevprev1 && !use_internal_x && !use_internal_y && !use_prev2 && !use_prev1)
    );

    // m1_enters always forces both previous-value outputs high.
    check_m1_forces_prev_outputs: assert property (
        @(posedge clk)
        m1_enters |-> (use_prevprev1 && use_prev1)
    );

    // Internal path selects can only assert when c2_enters is high.
    check_internal_selects_require_c2: assert property (
        @(posedge clk)
        (use_internal_x || use_internal_y) |-> c2_enters
    );

endmodule