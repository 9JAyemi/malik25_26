module my_module_sva (
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);
    // Note: No clock or reset in RTL; sample on posedge of relevant signals.

    // Y must equal the 4-input NAND of A1,A2,B1,B2.
    check_y_is_nand: assert property (
        @(posedge A1 or posedge A2 or posedge B1 or posedge B2 or posedge Y)
        (Y == ~(A1 & A2 & B1 & B2))
    );

    // When all inputs are HIGH, Y must be LOW.
    check_y_low_when_all_high: assert property (
        @(posedge A1 or posedge A2 or posedge B1 or posedge B2 or posedge Y)
        (A1 && A2 && B1 && B2) |-> (Y == 1'b0)
    );

    // When any input is LOW, Y must be HIGH.
    check_y_high_when_any_low: assert property (
        @(posedge A1 or posedge A2 or posedge B1 or posedge B2 or posedge Y)
        ((!A1) || (!A2) || (!B1) || (!B2)) |-> (Y == 1'b1)
    );

    // A1 LOW forces Y HIGH.
    check_y_high_when_A1_low: assert property (
        @(posedge A1 or posedge A2 or posedge B1 or posedge B2 or posedge Y)
        (!A1) |-> (Y == 1'b1)
    );

    // A2 LOW forces Y HIGH.
    check_y_high_when_A2_low: assert property (
        @(posedge A1 or posedge A2 or posedge B1 or posedge B2 or posedge Y)
        (!A2) |-> (Y == 1'b1)
    );

    // B1 LOW forces Y HIGH.
    check_y_high_when_B1_low: assert property (
        @(posedge A1 or posedge A2 or posedge B1 or posedge B2 or posedge Y)
        (!B1) |-> (Y == 1'b1)
    );

    // B2 LOW forces Y HIGH.
    check_y_high_when_B2_low: assert property (
        @(posedge A1 or posedge A2 or posedge B1 or posedge B2 or posedge Y)
        (!B2) |-> (Y == 1'b1)
    );

    // Y can be LOW only if all inputs are HIGH.
    check_y_zero_implies_all_high: assert property (
        @(posedge A1 or posedge A2 or posedge B1 or posedge B2 or posedge Y)
        (Y == 1'b0) |-> (A1 && A2 && B1 && B2)
    );

endmodule