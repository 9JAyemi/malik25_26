module module_name_sva (
    input logic clk,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic Y
);

    // Y must match the RTL Boolean expression on every sample.
    check_y_matches_rtl_function: assert property (
        @(posedge clk)
        Y == (((A1 & A2 & A3 & ~B1) | (~A1 & ~A2 & ~A3 & B1)) ? 1'b1 : 1'b0)
    );

    // All A inputs high with B1 low must drive Y high.
    check_all_high_and_b1_low_sets_y: assert property (
        @(posedge clk)
        (A1 && A2 && A3 && !B1) |-> Y
    );

    // All A inputs low with B1 high must drive Y high.
    check_all_low_and_b1_high_sets_y: assert property (
        @(posedge clk)
        (!A1 && !A2 && !A3 && B1) |-> Y
    );

    // With B1 low, any low A input must force Y low.
    check_b1_low_nonmatch_clears_y: assert property (
        @(posedge clk)
        (!B1 && (!A1 || !A2 || !A3)) |-> !Y
    );

    // With B1 high, any high A input must force Y low.
    check_b1_high_nonmatch_clears_y: assert property (
        @(posedge clk)
        (B1 && (A1 || A2 || A3)) |-> !Y
    );

    // A high Y is only allowed for the two encoded input patterns.
    check_y_high_only_for_encoded_patterns: assert property (
        @(posedge clk)
        Y |-> ((A1 && A2 && A3 && !B1) || (!A1 && !A2 && !A3 && B1))
    );

    // If the A inputs are not all equal, Y must remain low.
    check_mixed_a_inputs_force_y_low: assert property (
        @(posedge clk)
        ((A1 ^ A2) || (A2 ^ A3)) |-> !Y
    );

endmodule