module two_to_one_mux_sva (
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);
    // No clock or reset in RTL; pure combinational 2:1 mux with select=B1 and Y=(B1?A2:A1).
    wire select = B1;

    // Core mux function holds when sampled on A1 rising edge.
    check_mux_func_on_a1: assert property (
        @(posedge A1) Y == ((select == 1'b0) ? A1 : A2)
    );

    // Core mux function holds when sampled on A2 rising edge.
    check_mux_func_on_a2: assert property (
        @(posedge A2) Y == ((select == 1'b0) ? A1 : A2)
    );

    // Core mux function holds when sampled on B1 rising edge.
    check_mux_func_on_b1: assert property (
        @(posedge B1) Y == ((select == 1'b0) ? A1 : A2)
    );

    // When select=0 and A1 rises, Y must be 1 (follows A1).
    check_follow_a1_sel0: assert property (
        @(posedge A1) (select == 1'b0) |-> (Y == 1'b1)
    );

    // When select=1 and A2 rises, Y must be 1 (follows A2).
    check_follow_a2_sel1: assert property (
        @(posedge A2) (select == 1'b1) |-> (Y == 1'b1)
    );

    // On select rising edge (select=1), Y equals A2.
    check_y_eq_a2_on_b1rise: assert property (
        @(posedge B1) (Y == A2)
    );

    // If A1==A2 at sample, Y equals that common value.
    check_equal_inputs_propagate: assert property (
        @(posedge A1) (A1 == A2) |-> (Y == A1)
    );

    // When Y rises, the selected input must be high at that instant.
    check_y_posedge_consistency: assert property (
        @(posedge Y) Y == ((select == 1'b0) ? A1 : A2)
    );

endmodule