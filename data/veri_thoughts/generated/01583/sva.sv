module sky130_fd_sc_ms__a211oi_sva (
    input logic CLK,
    input logic RESETn,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1
);
    // No clock/reset in RTL; pure combinational: Y = ~((A1 & A2) | B1 | C1). Sampled on CLK, gated by active-low RESETn.

    // Y equals NOR of (A1&A2), B1, and C1.
    check_function_equivalence: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (Y == ~( (A1 & A2) | B1 | C1 ))
    );

    // If B1 is HIGH, Y must be LOW.
    check_y_low_when_b1_high: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (B1) |-> (Y == 1'b0)
    );

    // If C1 is HIGH, Y must be LOW.
    check_y_low_when_c1_high: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (C1) |-> (Y == 1'b0)
    );

    // If A1&A2 are HIGH, Y must be LOW.
    check_y_low_when_a1a2_high: assert property (
        @(posedge CLK) disable iff (!RESETn)
        ((A1 & A2) == 1'b1) |-> (Y == 1'b0)
    );

    // If none of the three OR terms are HIGH, Y must be HIGH.
    check_y_high_when_all_terms_low: assert property (
        @(posedge CLK) disable iff (!RESETn)
        ((A1 & A2) == 1'b0 && B1 == 1'b0 && C1 == 1'b0) |-> (Y == 1'b1)
    );

    // Y HIGH implies all three OR terms are LOW.
    check_y_high_implies_all_terms_low: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (Y == 1'b1) |-> ((A1 & A2) == 1'b0 && B1 == 1'b0 && C1 == 1'b0)
    );

    // With B1=0 and C1=0, Y equals NOT(A1&A2).
    check_conditional_eq_when_b1c1_zero: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (B1 == 1'b0 && C1 == 1'b0) |-> (Y == ~(A1 & A2))
    );

    // If Y is LOW while B1=0 and C1=0, then A1&A2 must be HIGH.
    check_y_low_with_b1c1_zero_implies_a1a2_high: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (Y == 1'b0 && B1 == 1'b0 && C1 == 1'b0) |-> ((A1 & A2) == 1'b1)
    );

    // If Y is LOW and A1&A2 is LOW, then either B1 or C1 must be HIGH.
    check_y_low_with_a1a2_low_implies_b1orc1_high: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (Y == 1'b0 && (A1 & A2) == 1'b0) |-> (B1 == 1'b1 || C1 == 1'b1)
    );

    // If any OR term is HIGH, Y must be LOW.
    check_y_low_when_any_term_high: assert property (
        @(posedge CLK) disable iff (!RESETn)
        (((A1 & A2) == 1'b1) || (B1 == 1'b1) || (C1 == 1'b1)) |-> (Y == 1'b0)
    );

endmodule