module sky130_fd_sc_lp__a311oi_sva (
    input logic CLK,   // sampling clock for SVA (DUT has no clock/reset)
    input logic Y,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic C1
);
    // Y must equal ~((A1 & A2 & A3) | B1 | C1).
    check_function_equivalence: assert property (
        @(posedge CLK) Y == ~((A1 & A2 & A3) | B1 | C1)
    );

    // If B1 is HIGH, Y must be LOW.
    check_b1_high_forces_y_low: assert property (
        @(posedge CLK) B1 |-> (Y == 1'b0)
    );

    // If C1 is HIGH, Y must be LOW.
    check_c1_high_forces_y_low: assert property (
        @(posedge CLK) C1 |-> (Y == 1'b0)
    );

    // If A1&A2&A3 is HIGH, Y must be LOW.
    check_and3_high_forces_y_low: assert property (
        @(posedge CLK) (A1 & A2 & A3) |-> (Y == 1'b0)
    );

    // If either B1 or C1 is HIGH, Y must be LOW.
    check_b1_or_c1_high_forces_y_low: assert property (
        @(posedge CLK) (B1 || C1) |-> (Y == 1'b0)
    );

    // With B1=0 and C1=0, Y reduces to ~(A1 & A2 & A3).
    check_reduction_when_b1c1_low: assert property (
        @(posedge CLK) (!B1 && !C1) |-> (Y == ~(A1 & A2 & A3))
    );

    // If B1=0, C1=0, and A1=0, then Y must be HIGH.
    check_a1_zero_with_b1c1_zero_y_one: assert property (
        @(posedge CLK) (!B1 && !C1 && !A1) |-> (Y == 1'b1)
    );

    // If B1=0, C1=0, and A2=0, then Y must be HIGH.
    check_a2_zero_with_b1c1_zero_y_one: assert property (
        @(posedge CLK) (!B1 && !C1 && !A2) |-> (Y == 1'b1)
    );

    // If B1=0, C1=0, and A3=0, then Y must be HIGH.
    check_a3_zero_with_b1c1_zero_y_one: assert property (
        @(posedge CLK) (!B1 && !C1 && !A3) |-> (Y == 1'b1)
    );

    // If all inputs are LOW, Y must be HIGH.
    check_all_zero_inputs_y_one: assert property (
        @(posedge CLK) (!A1 && !A2 && !A3 && !B1 && !C1) |-> (Y == 1'b1)
    );

    // Y HIGH implies B1=0, C1=0, and not (A1&A2&A3).
    check_y_high_implies_inputs_not_asserting: assert property (
        @(posedge CLK) Y |-> (!B1 && !C1 && !(A1 & A2 & A3))
    );

    // Y LOW implies at least one of (B1, C1, A1&A2&A3) is HIGH.
    check_y_low_implies_some_input_asserting: assert property (
        @(posedge CLK) (Y == 1'b0) |-> (B1 || C1 || (A1 & A2 & A3))
    );

endmodule