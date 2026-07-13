module top_module_sva (
    input logic CLK,        // External verification clock (RTL has no clock/reset)
    input logic A, B, C, D, // DUT inputs
    input logic [1:0] X,    // DUT outputs
    input logic Y,
    input logic Z
);
    // Y reflects if any input is HIGH.
    check_y_is_or: assert property (
        @(posedge CLK) Y == (A || B || C || D)
    );

    // Z reflects if any input is HIGH (priority mux of 1-bit inputs == OR).
    check_z_is_or: assert property (
        @(posedge CLK) Z == (A || B || C || D)
    );

    // Y and Z are identical for all input combinations.
    check_y_equals_z: assert property (
        @(posedge CLK) Z == Y
    );

    // If A is HIGH, X=0 and Y=Z=1 (A has highest priority).
    check_a_has_priority: assert property (
        @(posedge CLK) A |-> (X == 2'd0) && (Y == 1'b1) && (Z == 1'b1)
    );

    // If A is LOW and B is HIGH, X=1 and Y=Z=1.
    check_b_selected_when_a0: assert property (
        @(posedge CLK) (!A && B) |-> (X == 2'd1) && (Y == 1'b1) && (Z == 1'b1)
    );

    // If A,B are LOW and C is HIGH, X=2 and Y=Z=1.
    check_c_selected_when_ab0: assert property (
        @(posedge CLK) (!A && !B && C) |-> (X == 2'd2) && (Y == 1'b1) && (Z == 1'b1)
    );

    // If A,B,C are LOW and D is HIGH, X=3 and Y=Z=1.
    check_d_selected_when_abc0: assert property (
        @(posedge CLK) (!A && !B && !C && D) |-> (X == 2'd3) && (Y == 1'b1) && (Z == 1'b1)
    );

    // If all inputs are LOW, X=0 and Y=Z=0 (default case).
    check_default_when_none_high: assert property (
        @(posedge CLK) (!A && !B && !C && !D) |-> (X == 2'd0) && (Y == 1'b0) && (Z == 1'b0)
    );

    // If Y=1 and X=0, then A must be HIGH.
    check_decode_unique_a: assert property (
        @(posedge CLK) (Y && (X == 2'd0)) |-> A
    );

    // If Y=1 and X=1, then !A and B must be true.
    check_decode_unique_b: assert property (
        @(posedge CLK) (Y && (X == 2'd1)) |-> (!A && B)
    );

    // If Y=1 and X=2, then !A,!B and C must be true.
    check_decode_unique_c: assert property (
        @(posedge CLK) (Y && (X == 2'd2)) |-> (!A && !B && C)
    );

    // If Y=1 and X=3, then !A,!B,!C and D must be true.
    check_decode_unique_d: assert property (
        @(posedge CLK) (Y && (X == 2'd3)) |-> (!A && !B && !C && D)
    );

    // If Y=0, then all inputs must be LOW.
    check_y_zero_means_no_inputs: assert property (
        @(posedge CLK) (!Y) |-> (!A && !B && !C && !D)
    );

    // When A and any other input are HIGH, A's priority selects X=0 and Y=Z=1.
    check_overshadowing_when_a_and_others: assert property (
        @(posedge CLK) (A && (B || C || D)) |-> (X == 2'd0) && (Y == 1'b1) && (Z == 1'b1)
    );

    // When A=0 and B with (C or D) are HIGH, B's priority selects X=1 and Y=Z=1.
    check_overshadowing_when_b_over_cd: assert property (
        @(posedge CLK) (!A && B && (C || D)) |-> (X == 2'd1) && (Y == 1'b1) && (Z == 1'b1)
    );

    // When A=B=0 and C&D are HIGH, C's priority selects X=2 and Y=Z=1.
    check_overshadowing_when_c_over_d: assert property (
        @(posedge CLK) (!A && !B && C && D) |-> (X == 2'd2) && (Y == 1'b1) && (Z == 1'b1)
    );
endmodule