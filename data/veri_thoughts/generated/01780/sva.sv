module sky130_fd_sc_hd__a31oi_sva (
    input logic Y,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1
);
    // Y equals ~(B1 | (A1 & A2 & A3)) sampled on A1 rising.
    function_equivalence_on_a1: assert property (
        @(posedge A1) (Y == ~(B1 | (A1 & A2 & A3)))
    );

    // Y equals ~(B1 | (A1 & A2 & A3)) sampled on A2 rising.
    function_equivalence_on_a2: assert property (
        @(posedge A2) (Y == ~(B1 | (A1 & A2 & A3)))
    );

    // Y equals ~(B1 | (A1 & A2 & A3)) sampled on A3 rising.
    function_equivalence_on_a3: assert property (
        @(posedge A3) (Y == ~(B1 | (A1 & A2 & A3)))
    );

    // Y equals ~(B1 | (A1 & A2 & A3)) sampled on B1 rising.
    function_equivalence_on_b1: assert property (
        @(posedge B1) (Y == ~(B1 | (A1 & A2 & A3)))
    );

    // Y equals ~(B1 | (A1 & A2 & A3)) sampled on Y rising.
    function_equivalence_on_y: assert property (
        @(posedge Y) (Y == ~(B1 | (A1 & A2 & A3)))
    );

    // If Y is HIGH then B1 must be LOW and not all A's are HIGH.
    y_high_implies_inputs_conditions: assert property (
        @(posedge Y) (B1 == 1'b0) && ((A1 == 1'b0) || (A2 == 1'b0) || (A3 == 1'b0))
    );

    // When B1 rises HIGH, Y must be driven LOW.
    b1_high_forces_y_low: assert property (
        @(posedge B1) (Y == 1'b0)
    );

    // When all A's are HIGH, Y must be LOW (sampled on A1 rising).
    all_a_high_forces_y_low_on_a1: assert property (
        @(posedge A1) ((A1 & A2 & A3) |-> (Y == 1'b0))
    );

    // When all A's are HIGH, Y must be LOW (sampled on A2 rising).
    all_a_high_forces_y_low_on_a2: assert property (
        @(posedge A2) ((A1 & A2 & A3) |-> (Y == 1'b0))
    );

    // When all A's are HIGH, Y must be LOW (sampled on A3 rising).
    all_a_high_forces_y_low_on_a3: assert property (
        @(posedge A3) ((A1 & A2 & A3) |-> (Y == 1'b0))
    );
endmodule