module sky130_fd_sc_hd__o221ai_sva (
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic C1
);
    // Y equals ~((A1|A2)&(B1|B2)&C1) sampled on A1 rising.
    function_eq_on_A1: assert property (
        @(posedge A1) disable iff (1'b0) Y == ~(((A1 | A2) & (B1 | B2) & C1))
    );
    // Y equals ~((A1|A2)&(B1|B2)&C1) sampled on A2 rising.
    function_eq_on_A2: assert property (
        @(posedge A2) disable iff (1'b0) Y == ~(((A1 | A2) & (B1 | B2) & C1))
    );
    // Y equals ~((A1|A2)&(B1|B2)&C1) sampled on B1 rising.
    function_eq_on_B1: assert property (
        @(posedge B1) disable iff (1'b0) Y == ~(((A1 | A2) & (B1 | B2) & C1))
    );
    // Y equals ~((A1|A2)&(B1|B2)&C1) sampled on B2 rising.
    function_eq_on_B2: assert property (
        @(posedge B2) disable iff (1'b0) Y == ~(((A1 | A2) & (B1 | B2) & C1))
    );
    // Y equals ~((A1|A2)&(B1|B2)&C1) sampled on C1 rising.
    function_eq_on_C1: assert property (
        @(posedge C1) disable iff (1'b0) Y == ~(((A1 | A2) & (B1 | B2) & C1))
    );

    // C1 LOW forces Y HIGH.
    c1_low_forces_y_high: assert property (
        @(posedge A1) disable iff (1'b0) (C1 == 1'b0) |-> (Y == 1'b1)
    );
    // Both A inputs LOW force Y HIGH.
    both_a_low_force_y_high: assert property (
        @(posedge B1) disable iff (1'b0) ((A1 == 1'b0) && (A2 == 1'b0)) |-> (Y == 1'b1)
    );
    // Both B inputs LOW force Y HIGH.
    both_b_low_force_y_high: assert property (
        @(posedge A2) disable iff (1'b0) ((B1 == 1'b0) && (B2 == 1'b0)) |-> (Y == 1'b1)
    );
    // All terms HIGH force Y LOW.
    all_terms_high_force_y_low: assert property (
        @(posedge B2) disable iff (1'b0) (((A1 | A2) == 1'b1) && ((B1 | B2) == 1'b1) && (C1 == 1'b1)) |-> (Y == 1'b0)
    );
    // Y LOW implies C1 and both OR terms are HIGH.
    y_low_requires_all_terms_high: assert property (
        @(posedge C1) disable iff (1'b0) (Y == 1'b0) |-> (((A1 | A2) == 1'b1) && ((B1 | B2) == 1'b1) && (C1 == 1'b1))
    );
endmodule