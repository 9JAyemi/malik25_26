module circuit_sva (
    input logic clk,   // sampling clock for assertions (DUT has no clock/reset)
    input logic Y,
    input logic A1_N,
    input logic A2_N,
    input logic B1,
    input logic B2,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);
    ///// Functional equivalence (same-cycle) /////
    // Y is 1 when either product term is true.
    check_y_high_when_term1_or_term2: assert property (
        @(posedge clk) disable iff (1'b0)
        ((A1_N & A2_N & ~B1 & ~B2) | (A1_N & ~A2_N & B1 & B2)) |=> Y
    );
    // Y is 0 when neither product term is true.
    check_y_low_when_neither_term: assert property (
        @(posedge clk) disable iff (1'b0)
        !((A1_N & A2_N & ~B1 & ~B2) | (A1_N & ~A2_N & B1 & B2)) |=> !Y
    );

    ///// Simple implications derived from the equation /////
    // If A1_N is LOW, Y must be LOW.
    check_a1n_low_forces_y_low: assert property (
        @(posedge clk) disable iff (1'b0)
        !A1_N |=> !Y
    );
    // If B1 and B2 differ, Y must be LOW.
    check_mismatched_b_forces_y_low: assert property (
        @(posedge clk) disable iff (1'b0)
        (B1 ^ B2) |=> !Y
    );
    // If Y is HIGH, A1_N must be HIGH.
    check_y_high_requires_a1n_high: assert property (
        @(posedge clk) disable iff (1'b0)
        Y |=> A1_N
    );
    // If Y is HIGH, B1 and B2 must be equal (00 or 11).
    check_y_high_requires_b_equal: assert property (
        @(posedge clk) disable iff (1'b0)
        Y |=> !(B1 ^ B2)
    );

    ///// Positive cases for Y=1 /////
    // When A1_N&A2_N&~B1&~B2, Y must be 1.
    check_term1_drives_y_high: assert property (
        @(posedge clk) disable iff (1'b0)
        (A1_N & A2_N & ~B1 & ~B2) |=> Y
    );
    // When A1_N&~A2_N&B1&B2, Y must be 1.
    check_term2_drives_y_high: assert property (
        @(posedge clk) disable iff (1'b0)
        (A1_N & ~A2_N & B1 & B2) |=> Y
    );

    ///// Negative cases for Y=0 /////
    // With B1=B2=0, Y is 0 unless A1_N&A2_N.
    check_b00_requires_a1n_a2n_for_y_high: assert property (
        @(posedge clk) disable iff (1'b0)
        ((B1==1'b0) && (B2==1'b0) && !(A1_N && A2_N)) |=> !Y
    );
    // With B1=B2=1, Y is 0 unless A1_N&~A2_N.
    check_b11_requires_a1n_and_not_a2n_for_y_high: assert property (
        @(posedge clk) disable iff (1'b0)
        (B1 && B2 && !(A1_N && !A2_N)) |=> !Y
    );

    ///// Stability properties /////
    // If A1_N,A2_N,B1,B2 are stable, Y must be stable.
    check_y_stable_when_inputs_stable: assert property (
        @(posedge clk) disable iff (1'b0)
        (A1_N == $past(A1_N)) && (A2_N == $past(A2_N)) && (B1 == $past(B1)) && (B2 == $past(B2)) |-> (Y == $past(Y))
    );
    // Changes on power pins alone cannot change Y when logic inputs are stable.
    check_power_pin_independence: assert property (
        @(posedge clk) disable iff (1'b0)
        (A1_N == $past(A1_N)) && (A2_N == $past(A2_N)) && (B1 == $past(B1)) && (B2 == $past(B2)) &&
        ((VPWR != $past(VPWR)) || (VGND != $past(VGND)) || (VPB != $past(VPB)) || (VNB != $past(VNB)))
        |-> (Y == $past(Y))
    );
endmodule