module three_input_and_power_good_sva (
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic C1,
    input logic C2
);
    // No clock or reset in DUT; purely combinational; assertions sample on input posedges.
    // Functional intent: Y = ~(A1 & A2) & ~(B1 & B2) & ~(C1 & C2).

    // Y implements the intended boolean function when A1 rises.
    func_equiv_on_A1_pos: assert property (
        @(posedge A1) Y == ((~(A1 & A2)) & (~(B1 & B2)) & (~(C1 & C2)))
    );

    // Y implements the intended boolean function when A2 rises.
    func_equiv_on_A2_pos: assert property (
        @(posedge A2) Y == ((~(A1 & A2)) & (~(B1 & B2)) & (~(C1 & C2)))
    );

    // Y implements the intended boolean function when B1 rises.
    func_equiv_on_B1_pos: assert property (
        @(posedge B1) Y == ((~(A1 & A2)) & (~(B1 & B2)) & (~(C1 & C2)))
    );

    // Y implements the intended boolean function when B2 rises.
    func_equiv_on_B2_pos: assert property (
        @(posedge B2) Y == ((~(A1 & A2)) & (~(B1 & B2)) & (~(C1 & C2)))
    );

    // Y implements the intended boolean function when C1 rises.
    func_equiv_on_C1_pos: assert property (
        @(posedge C1) Y == ((~(A1 & A2)) & (~(B1 & B2)) & (~(C1 & C2)))
    );

    // Y implements the intended boolean function when C2 rises.
    func_equiv_on_C2_pos: assert property (
        @(posedge C2) Y == ((~(A1 & A2)) & (~(B1 & B2)) & (~(C1 & C2)))
    );

    // If A1&A2 are both HIGH, Y must be LOW (sampled on A1 rise).
    pairA_high_forces_Y_low_A1: assert property (
        @(posedge A1) (A1 & A2) |-> (Y == 1'b0)
    );

    // If B1&B2 are both HIGH, Y must be LOW (sampled on B1 rise).
    pairB_high_forces_Y_low_B1: assert property (
        @(posedge B1) (B1 & B2) |-> (Y == 1'b0)
    );

    // If C1&C2 are both HIGH, Y must be LOW (sampled on C1 rise).
    pairC_high_forces_Y_low_C1: assert property (
        @(posedge C1) (C1 & C2) |-> (Y == 1'b0)
    );

    // If Y is HIGH, no input pair can be simultaneously HIGH (sampled on Y rise).
    y_high_implies_no_pair_high: assert property (
        @(posedge Y) Y |-> (!(A1 & A2) && !(B1 & B2) && !(C1 & C2))
    );

endmodule