module sky130_fd_sc_hdll__a32oi_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic B2
);

    // Y matches the implemented OAI32 logic.
    check_oai32_function: assert property (
        @(posedge clk)
        Y == !((A1 && A2 && A3) || (B1 && B2))
    );

    // All three A inputs high force Y low.
    check_a_triplet_forces_low: assert property (
        @(posedge clk)
        (A1 && A2 && A3) |-> !Y
    );

    // Both B inputs high force Y low.
    check_b_pair_forces_low: assert property (
        @(posedge clk)
        (B1 && B2) |-> !Y
    );

    // Y is high when neither input product term is active.
    check_output_high_when_no_product_active: assert property (
        @(posedge clk)
        (!(A1 && A2 && A3) && !(B1 && B2)) |-> Y
    );

    // A low Y must be caused by at least one active product term.
    check_low_output_has_cause: assert property (
        @(posedge clk)
        !Y |-> ((A1 && A2 && A3) || (B1 && B2))
    );

    // Stable inputs keep the output stable.
    check_stable_inputs_hold_output: assert property (
        @(posedge clk)
        ($stable(A1) && $stable(A2) && $stable(A3) && $stable(B1) && $stable(B2)) |-> $stable(Y)
    );

    // A sampled output change requires a sampled input change.
    check_output_change_requires_input_change: assert property (
        @(posedge clk)
        $changed(Y) |-> ($changed(A1) || $changed(A2) || $changed(A3) || $changed(B1) || $changed(B2))
    );

endmodule