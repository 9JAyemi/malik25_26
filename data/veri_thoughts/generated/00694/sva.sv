module mux2to1_sva (
    input logic clk,
    input logic A1_N,
    input logic A2_N,
    input logic B1,
    input logic B2,
    input logic Y
);
    // Local mirrors of RTL internal nets
    wire A1 = ~A1_N;
    wire A2 = ~A2_N;

    // Y implements the exact RTL sum-of-products expression.
    check_function_sop: assert property (
        @(posedge clk) Y == ((A1 & A2 & B2) | (A1 & ~A2 & B1) | (~A1 & A2 & B2) | (~A1 & ~A2 & B1))
    );

    // Y equals mux form: A2_N=1 selects B1, A2_N=0 selects B2.
    check_function_mux_form: assert property (
        @(posedge clk) Y == ((~A2_N & B2) | (A2_N & B1))
    );

    // When select is HIGH (A2_N=1), Y must equal B1.
    check_select_high_b1: assert property (
        @(posedge clk) (A2_N == 1'b1) |-> (Y == B1)
    );

    // When select is LOW (A2_N=0), Y must equal B2.
    check_select_low_b2: assert property (
        @(posedge clk) (A2_N == 1'b0) |-> (Y == B2)
    );

    // Changing A1_N alone must not change Y.
    check_a1n_no_effect: assert property (
        @(posedge clk) (!$initstate && $changed(A1_N) && $stable(A2_N) && $stable(B1) && $stable(B2)) |-> (Y == $past(Y))
    );

    // If B1==B2, Y must equal that common value.
    check_equal_inputs_pass_through: assert property (
        @(posedge clk) (B1 == B2) |-> (Y == B1)
    );

    // Changing select with equal inputs must not change Y.
    check_no_change_on_sel_when_inputs_equal: assert property (
        @(posedge clk) (!$initstate && $changed(A2_N) && $stable(B1) && $stable(B2) && (B1 == B2)) |-> (Y == $past(Y))
    );

    // Changing select with different inputs must toggle Y.
    check_toggle_on_sel_when_inputs_differ: assert property (
        @(posedge clk) (!$initstate && $changed(A2_N) && $stable(B1) && $stable(B2) && (B1 != B2)) |-> (Y != $past(Y))
    );

    // With select HIGH, changing B1 alone must toggle Y.
    check_follow_b1_when_sel_high: assert property (
        @(posedge clk) (!$initstate && (A2_N == 1'b1) && $changed(B1) && $stable(A2_N) && $stable(B2)) |-> (Y != $past(Y))
    );

    // With select LOW, changing B2 alone must toggle Y.
    check_follow_b2_when_sel_low: assert property (
        @(posedge clk) (!$initstate && (A2_N == 1'b0) && $changed(B2) && $stable(A2_N) && $stable(B1)) |-> (Y != $past(Y))
    );

    // With select HIGH, changing B2 alone must not change Y.
    check_ignore_b2_when_sel_high: assert property (
        @(posedge clk) (!$initstate && (A2_N == 1'b1) && $changed(B2) && $stable(A2_N) && $stable(B1)) |-> (Y == $past(Y))
    );

    // With select LOW, changing B1 alone must not change Y.
    check_ignore_b1_when_sel_low: assert property (
        @(posedge clk) (!$initstate && (A2_N == 1'b0) && $changed(B1) && $stable(A2_N) && $stable(B2)) |-> (Y == $past(Y))
    );
endmodule