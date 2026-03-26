module logical_operation_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1,
    input logic D1
);

    // Overall output matches the RTL conditional expression.
    check_y_matches_rtl_expression: assert property (
        @(posedge clk)
        Y == ((A1 & A2) ? 1'b1 :
              (A1 & !A2) ? B1 :
              (!A1 & A2) ? C1 :
              (!A1 & !A2 & !B1 & !C1) ? D1 :
              1'b0)
    );

    // When A1 and A2 are high, Y is forced high.
    check_y_high_when_a1_a2_high: assert property (
        @(posedge clk) (A1 && A2) |-> (Y == 1'b1)
    );

    // When A1 is high and A2 is low, Y follows B1.
    check_y_follows_b1_when_a1_high_a2_low: assert property (
        @(posedge clk) (A1 && !A2) |-> (Y == B1)
    );

    // When A1 is low and A2 is high, Y follows C1.
    check_y_follows_c1_when_a1_low_a2_high: assert property (
        @(posedge clk) (!A1 && A2) |-> (Y == C1)
    );

    // When A1 and A2 are low and B1/C1 are low, Y follows D1.
    check_y_follows_d1_in_low_low_zero_case: assert property (
        @(posedge clk) (!A1 && !A2 && !B1 && !C1) |-> (Y == D1)
    );

    // When A1 and A2 are low and either B1 or C1 is high, Y is low.
    check_y_low_in_low_low_nonzero_bc_case: assert property (
        @(posedge clk) (!A1 && !A2 && (B1 || C1)) |-> (Y == 1'b0)
    );

endmodule