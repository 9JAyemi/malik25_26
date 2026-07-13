module sky130_fd_sc_ms__o31ai_sva (
    input logic Y,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1
);
    // Use edges of all ports as the sampling clock for this purely combinational cell.
    default clocking cb @(posedge A1 or negedge A1 or
                          posedge A2 or negedge A2 or
                          posedge A3 or negedge A3 or
                          posedge B1 or negedge B1 or
                          posedge Y  or negedge Y);
    endclocking

    ///// Combinational function /////
    // Y implements ~(B1 & (A1 | A2 | A3)).
    check_truth_function: assert property (
        Y == ~(B1 & (A1 | A2 | A3))
    );

    ///// Useful implications of the function /////
    // If B1 is LOW, Y must be HIGH.
    check_y_high_when_b1_low: assert property (
        (!B1) |-> (Y == 1'b1)
    );

    // If B1 is HIGH and any A input is HIGH, Y must be LOW.
    check_y_low_when_b1_and_any_a: assert property (
        (B1 && (A1 || A2 || A3)) |-> (Y == 1'b0)
    );

    // If B1 is HIGH and all A inputs are LOW, Y must be HIGH.
    check_y_high_when_b1_and_all_a_low: assert property (
        (B1 && !A1 && !A2 && !A3) |-> (Y == 1'b1)
    );

    // If Y is LOW, then B1 is HIGH and at least one A input is HIGH.
    check_y_low_implies_b1_and_some_a: assert property (
        (Y == 1'b0) |-> (B1 && (A1 || A2 || A3))
    );

    // If Y is HIGH, then B1 is LOW or all A inputs are LOW.
    check_y_high_implies_b1_low_or_all_a_low: assert property (
        (Y == 1'b1) |-> ((!B1) || (!A1 && !A2 && !A3))
    );

    // If B1 and A1 are HIGH, Y must be LOW.
    check_y_low_when_b1_and_a1: assert property (
        (B1 && A1) |-> (Y == 1'b0)
    );

    // If B1 and A2 are HIGH, Y must be LOW.
    check_y_low_when_b1_and_a2: assert property (
        (B1 && A2) |-> (Y == 1'b0)
    );

    // If B1 and A3 are HIGH, Y must be LOW.
    check_y_low_when_b1_and_a3: assert property (
        (B1 && A3) |-> (Y == 1'b0)
    );

endmodule