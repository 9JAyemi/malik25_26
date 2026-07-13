module mux_2to1_sva (
    input logic clk,    // sampling clock for assertions
    input logic A,
    input logic B,
    input logic S,
    input logic Y
);

    // Y must equal selected input per S.
    check_mux_function: assert property (
        @(posedge clk) Y == (S ? B : A)
    );

    // When S==0, Y equals A.
    check_select_zero_path: assert property (
        @(posedge clk) (S == 1'b0) |-> (Y == A)
    );

    // When S==1, Y equals B.
    check_select_one_path: assert property (
        @(posedge clk) (S == 1'b1) |-> (Y == B)
    );

    // If A,B,S are unchanged from last cycle, Y must be unchanged.
    check_stable_when_inputs_stable: assert property (
        @(posedge clk)
            (!$isunknown($past(A)) && !$isunknown($past(B)) && !$isunknown($past(S)) && !$isunknown($past(Y)) &&
             (A == $past(A)) && (B == $past(B)) && (S == $past(S))) |-> (Y == $past(Y))
    );

    // With S held at 0 across cycles, a change on A is reflected on Y.
    check_follow_A_when_S0: assert property (
        @(posedge clk)
            (!$isunknown($past(S)) &&
             ($past(S) == 1'b0) && (S == 1'b0) &&
             !$isunknown($past(A)) && (A != $past(A))) |-> (Y == A)
    );

    // With S held at 1 across cycles, a change on B is reflected on Y.
    check_follow_B_when_S1: assert property (
        @(posedge clk)
            (!$isunknown($past(S)) &&
             ($past(S) == 1'b1) && (S == 1'b1) &&
             !$isunknown($past(B)) && (B != $past(B))) |-> (Y == B)
    );

    // With S held at 0 and A stable, changes on B do not affect Y.
    check_ignore_B_when_S0: assert property (
        @(posedge clk)
            (!$isunknown($past(S)) && !$isunknown($past(A)) && !$isunknown($past(B)) && !$isunknown($past(Y)) &&
             ($past(S) == 1'b0) && (S == 1'b0) &&
             (A == $past(A)) && (B != $past(B))) |-> (Y == $past(Y))
    );

    // With S held at 1 and B stable, changes on A do not affect Y.
    check_ignore_A_when_S1: assert property (
        @(posedge clk)
            (!$isunknown($past(S)) && !$isunknown($past(A)) && !$isunknown($past(B)) && !$isunknown($past(Y)) &&
             ($past(S) == 1'b1) && (S == 1'b1) &&
             (B == $past(B)) && (A != $past(A))) |-> (Y == $past(Y))
    );

endmodule