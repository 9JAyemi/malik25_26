module and_or_module_sva (
    input logic clk,
    input logic a,
    input logic b,
    input logic g_out,
    input logic p_out
);

    // g_out must equal the AND of a and b.
    check_g_out_matches_and: assert property (
        @(posedge clk) g_out == (a & b)
    );

    // p_out must equal the OR of a and b.
    check_p_out_matches_or: assert property (
        @(posedge clk) p_out == (a | b)
    );

    // Both outputs must be low when both inputs are low.
    check_both_low_case: assert property (
        @(posedge clk) (!a && !b) |-> (!g_out && !p_out)
    );

    // Both outputs must be high when both inputs are high.
    check_both_high_case: assert property (
        @(posedge clk) (a && b) |-> (g_out && p_out)
    );

    // g_out must be low when a is low.
    check_g_out_low_when_a_low: assert property (
        @(posedge clk) !a |-> !g_out
    );

    // g_out must be low when b is low.
    check_g_out_low_when_b_low: assert property (
        @(posedge clk) !b |-> !g_out
    );

    // p_out must be high when a is high.
    check_p_out_high_when_a_high: assert property (
        @(posedge clk) a |-> p_out
    );

    // p_out must be high when b is high.
    check_p_out_high_when_b_high: assert property (
        @(posedge clk) b |-> p_out
    );

endmodule