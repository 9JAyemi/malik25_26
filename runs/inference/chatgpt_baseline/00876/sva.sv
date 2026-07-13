module three_to_one_sva (
    input logic CLK,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic Y
);
    ///// Functional equivalence /////
    // Y must equal (A1 & A2) | B1.
    check_y_function: assert property (
        @(posedge CLK) Y == ((A1 & A2) | B1)
    );

    ///// Basic implications /////
    // If B1 is HIGH, Y must be HIGH.
    check_y_when_b1_high: assert property (
        @(posedge CLK) B1 |-> (Y == 1'b1)
    );
    // If B1 is LOW, Y equals A1 & A2.
    check_y_when_b1_low: assert property (
        @(posedge CLK) !B1 |-> (Y == (A1 & A2))
    );
    // If A1 & A2 is TRUE, Y must be HIGH.
    check_y_when_and_true: assert property (
        @(posedge CLK) (A1 & A2) |-> (Y == 1'b1)
    );
    // If not (A1 & A2), Y equals B1.
    check_y_equals_b1_when_no_and: assert property (
        @(posedge CLK) !(A1 & A2) |-> (Y == B1)
    );

    ///// Output-to-input consistency /////
    // If Y is HIGH, then B1 is HIGH or (A1 & A2) is TRUE.
    check_y1_implies_sources: assert property (
        @(posedge CLK) (Y == 1'b1) |-> (B1 || (A1 & A2))
    );
    // If Y is LOW, then B1 is LOW and not (A1 & A2).
    check_y0_implies_blocked: assert property (
        @(posedge CLK) (Y == 1'b0) |-> (!B1 && !(A1 & A2))
    );

    ///// Edge-sensitive consequences (combinational propagation) /////
    // A rising edge on B1 forces Y HIGH.
    check_rose_b1_sets_y: assert property (
        @(posedge CLK) $rose(B1) |-> (Y == 1'b1)
    );
    // A falling edge on B1 drives Y LOW when A1 & A2 is FALSE.
    check_fell_b1_clears_y_when_and0: assert property (
        @(posedge CLK) ($fell(B1) && !(A1 & A2)) |-> (Y == 1'b0)
    );
    // A rising edge on A1 sets Y HIGH when A2 is HIGH and B1 is LOW.
    check_rose_a1_sets_y_when_gated: assert property (
        @(posedge CLK) ($rose(A1) && A2 && !B1) |-> (Y == 1'b1)
    );
    // A rising edge on A2 sets Y HIGH when A1 is HIGH and B1 is LOW.
    check_rose_a2_sets_y_when_gated: assert property (
        @(posedge CLK) ($rose(A2) && A1 && !B1) |-> (Y == 1'b1)
    );
    // A falling edge on A1 clears Y when B1 is LOW.
    check_fell_a1_clears_y_when_b1_low: assert property (
        @(posedge CLK) ($fell(A1) && !B1) |-> (Y == 1'b0)
    );
    // A falling edge on A2 clears Y when B1 is LOW.
    check_fell_a2_clears_y_when_b1_low: assert property (
        @(posedge CLK) ($fell(A2) && !B1) |-> (Y == 1'b0)
    );
endmodule