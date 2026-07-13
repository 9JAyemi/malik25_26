module boolean_func_sva (
    input logic clk,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB,
    input logic X
);

    // X must equal the implemented OR of the two product terms.
    check_x_matches_boolean_function: assert property (
        @(posedge clk) disable iff (1'b0)
            X == ((A1 & A2) | (B1 & B2 & VPWR & VGND & VPB & VNB))
    );

    // The A1/A2 product term alone is sufficient to drive X high.
    check_a_term_drives_x_high: assert property (
        @(posedge clk) disable iff (1'b0)
            (A1 & A2) |-> X
    );

    // The B1/B2 product term with all gating inputs high is sufficient to drive X high.
    check_b_term_drives_x_high: assert property (
        @(posedge clk) disable iff (1'b0)
            (B1 & B2 & VPWR & VGND & VPB & VNB) |-> X
    );

    // A high X must come from one of the two implemented product terms.
    check_x_high_has_valid_source: assert property (
        @(posedge clk) disable iff (1'b0)
            X |-> ((A1 & A2) | (B1 & B2 & VPWR & VGND & VPB & VNB))
    );

    // If neither product term is active, X must be low.
    check_x_low_without_active_terms: assert property (
        @(posedge clk) disable iff (1'b0)
            (!(A1 & A2) && !(B1 & B2 & VPWR & VGND & VPB & VNB)) |-> !X
    );

    // With the A term inactive, any low gating input blocks the B term from raising X.
    check_low_gate_blocks_b_term_when_a_term_inactive: assert property (
        @(posedge clk) disable iff (1'b0)
            (!(A1 & A2) && B1 && B2 && (!VPWR || !VGND || !VPB || !VNB)) |-> !X
    );

endmodule