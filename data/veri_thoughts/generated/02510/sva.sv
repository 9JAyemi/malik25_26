module sky130_fd_sc_hdll__a21o_sva (
    input logic A1,
    input logic A2,
    input logic B1,
    input logic X,
    input logic VPB,
    input logic VPWR,
    input logic VGND,
    input logic VNB
);
    // No explicit clock or reset; pure combinational; assertions sampled on input/power edges.

    // X equals A1 & A2 & B1 when sampled on A1's rising edge.
    check_x_eq_and_on_a1: assert property (
        @(posedge A1) X == (A1 & A2 & B1)
    );

    // X equals A1 & A2 & B1 when sampled on A2's rising edge.
    check_x_eq_and_on_a2: assert property (
        @(posedge A2) X == (A1 & A2 & B1)
    );

    // X equals A1 & A2 & B1 when sampled on B1's rising edge.
    check_x_eq_and_on_b1: assert property (
        @(posedge B1) X == (A1 & A2 & B1)
    );

    // When A2 and B1 are HIGH, X follows A1.
    check_follow_a1_when_others_high: assert property (
        @(posedge A1) (A2 && B1) |-> (X == A1)
    );

    // When A1 and B1 are HIGH, X follows A2.
    check_follow_a2_when_others_high: assert property (
        @(posedge A2) (A1 && B1) |-> (X == A2)
    );

    // When A1 and A2 are HIGH, X follows B1.
    check_follow_b1_when_others_high: assert property (
        @(posedge B1) (A1 && A2) |-> (X == B1)
    );

    // A rising X implies all inputs are HIGH (sampled on A1 edge).
    check_x_rise_requires_all_high: assert property (
        @(posedge A1) $rose(X) |-> (A1 && A2 && B1)
    );

    // A falling X implies at least one input is LOW (sampled on A1 edge).
    check_x_fall_requires_some_low: assert property (
        @(posedge A1) $fell(X) |-> (!A1 || !A2 || !B1)
    );

    // If A1/A2/B1 are stable, toggling VPWR cannot change X.
    check_x_stable_on_vpwr_toggle: assert property (
        @(posedge VPWR) ($stable(A1) && $stable(A2) && $stable(B1)) |-> $stable(X)
    );

    // If A1/A2/B1 are stable, toggling VGND cannot change X.
    check_x_stable_on_vgnd_toggle: assert property (
        @(posedge VGND) ($stable(A1) && $stable(A2) && $stable(B1)) |-> $stable(X)
    );
endmodule