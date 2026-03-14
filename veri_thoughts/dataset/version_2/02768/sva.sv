module nand_and_sva (
    input logic CLK,
    input logic A,
    input logic B,
    input logic Y
);
    // Y equals logical AND of A and B.
    check_function_and: assert property (
        @(posedge CLK) (Y == (A & B))
    );

    // If A is 0 then Y must be 0.
    check_y_zero_when_a_zero: assert property (
        @(posedge CLK) (A == 1'b0) |-> (Y == 1'b0)
    );

    // If B is 0 then Y must be 0.
    check_y_zero_when_b_zero: assert property (
        @(posedge CLK) (B == 1'b0) |-> (Y == 1'b0)
    );

    // If B is 1 then Y equals A.
    check_y_eq_a_when_b_one: assert property (
        @(posedge CLK) (B == 1'b1) |-> (Y == A)
    );

    // If A is 1 then Y equals B.
    check_y_eq_b_when_a_one: assert property (
        @(posedge CLK) (A == 1'b1) |-> (Y == B)
    );

    // If both inputs are stable, output is stable.
    check_inputs_stable_implies_y_stable: assert property (
        @(posedge CLK) ($stable(A) && $stable(B)) |-> $stable(Y)
    );

    // Y rising implies both inputs are 1.
    check_y_rise_requires_inputs_high: assert property (
        @(posedge CLK) $rose(Y) |-> (A == 1'b1 && B == 1'b1)
    );

    // Y falling implies at least one input is 0.
    check_y_fall_requires_any_input_low: assert property (
        @(posedge CLK) $fell(Y) |-> ((A == 1'b0) || (B == 1'b0))
    );

    // Y change implies at least one input changed.
    check_y_change_implies_input_change: assert property (
        @(posedge CLK) $changed(Y) |-> ($changed(A) || $changed(B))
    );

    // If both inputs are 1 then Y must be 1.
    check_high_when_both_high: assert property (
        @(posedge CLK) (A == 1'b1 && B == 1'b1) |-> (Y == 1'b1)
    );
endmodule