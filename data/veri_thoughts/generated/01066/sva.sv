module and_gate_sva (
    input logic Y,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic A4,
    input logic B1
);
    ///// AND gate functional correctness /////
    // Y equals the AND of all inputs whenever any input or Y rises.
    check_and_function_on_edges: assert property (
        @(posedge A1 or posedge A2 or posedge A3 or posedge A4 or posedge B1 or posedge Y)
        Y == (A1 & A2 & A3 & A4 & B1)
    );

    // Y can only rise when all inputs are HIGH.
    check_y_rise_requires_all_high: assert property (
        @(posedge Y)
        (A1 && A2 && A3 && A4 && B1)
    );

    // When all inputs are HIGH, Y must be HIGH.
    check_all_high_implies_y_high: assert property (
        @(posedge A1 or posedge A2 or posedge A3 or posedge A4 or posedge B1)
        (A1 && A2 && A3 && A4 && B1) |-> (Y == 1'b1)
    );

    // If any input is LOW, Y must be LOW.
    check_any_low_implies_y_low: assert property (
        @(posedge A1 or posedge A2 or posedge A3 or posedge A4 or posedge B1 or posedge Y)
        (!(A1 && A2 && A3 && A4 && B1)) |-> (Y == 1'b0)
    );

    // If B1 is LOW, Y must be LOW (gating by B1).
    check_b1_low_forces_y_low: assert property (
        @(posedge A1 or posedge A2 or posedge A3 or posedge A4 or posedge B1 or posedge Y)
        (!B1) |-> (Y == 1'b0)
    );

    // If A1 is LOW, Y must be LOW.
    check_a1_low_forces_y_low: assert property (
        @(posedge A1 or posedge A2 or posedge A3 or posedge A4 or posedge B1 or posedge Y)
        (!A1) |-> (Y == 1'b0)
    );

    // If A2 is LOW, Y must be LOW.
    check_a2_low_forces_y_low: assert property (
        @(posedge A1 or posedge A2 or posedge A3 or posedge A4 or posedge B1 or posedge Y)
        (!A2) |-> (Y == 1'b0)
    );

    // If A3 is LOW, Y must be LOW.
    check_a3_low_forces_y_low: assert property (
        @(posedge A1 or posedge A2 or posedge A3 or posedge A4 or posedge B1 or posedge Y)
        (!A3) |-> (Y == 1'b0)
    );

    // If A4 is LOW, Y must be LOW.
    check_a4_low_forces_y_low: assert property (
        @(posedge A1 or posedge A2 or posedge A3 or posedge A4 or posedge B1 or posedge Y)
        (!A4) |-> (Y == 1'b0)
    );
endmodule