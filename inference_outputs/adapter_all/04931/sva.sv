module mux_4to1_sva (
    input logic clk,
    input logic [1:0] S,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic Y
);

    // When S selects C, Y must equal C.
    check_select_c: assert property (
        @(posedge clk) (S == 2'b00) |-> (Y == C)
    );

    // When S selects D, Y must equal D.
    check_select_d: assert property (
        @(posedge clk) (S == 2'b01) |-> (Y == D)
    );

    // When S selects A, Y must equal A.
    check_select_a: assert property (
        @(posedge clk) (S == 2'b10) |-> (Y == A)
    );

    // When S selects B, Y must equal B.
    check_select_b: assert property (
        @(posedge clk) (S == 2'b11) |-> (Y == B)
    );

    // With S held at 00 and C stable, Y must remain stable.
    check_hold_when_c_selected: assert property (
        @(posedge clk) (S == 2'b00 && $stable(S) && $stable(C)) |-> $stable(Y)
    );

    // With S held at 01 and D stable, Y must remain stable.
    check_hold_when_d_selected: assert property (
        @(posedge clk) (S == 2'b01 && $stable(S) && $stable(D)) |-> $stable(Y)
    );

    // With S held at 10 and A stable, Y must remain stable.
    check_hold_when_a_selected: assert property (
        @(posedge clk) (S == 2'b10 && $stable(S) && $stable(A)) |-> $stable(Y)
    );

    // With S held at 11 and B stable, Y must remain stable.
    check_hold_when_b_selected: assert property (
        @(posedge clk) (S == 2'b11 && $stable(S) && $stable(B)) |-> $stable(Y)
    );

endmodule