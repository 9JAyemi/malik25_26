module mux_2_1_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic SEL,
    input logic Y
);

    // Y must always match the mux select equation.
    check_mux_equation: assert property (
        @(posedge clk) Y == (SEL ? B : A)
    );

    // When SEL is low, Y must follow A.
    check_select_low_routes_a: assert property (
        @(posedge clk) !SEL |-> (Y == A)
    );

    // When SEL is high, Y must follow B.
    check_select_high_routes_b: assert property (
        @(posedge clk) SEL |-> (Y == B)
    );

    // With SEL low and A stable, a change on B must not change Y.
    check_unselected_b_ignored_when_sel_low: assert property (
        @(posedge clk) (!SEL && $stable(A) && $changed(B)) |-> $stable(Y)
    );

    // With SEL high and B stable, a change on A must not change Y.
    check_unselected_a_ignored_when_sel_high: assert property (
        @(posedge clk) (SEL && $stable(B) && $changed(A)) |-> $stable(Y)
    );

    // With SEL low and A stable, a change on SEL must not change Y.
    check_sel_change_ignored_when_sel_low: assert property (
        @(posedge clk) (!SEL && $stable(A) && $changed(SEL)) |-> $stable(Y)
    );

    // With SEL high and B stable, a change on SEL must not change Y.
    check_sel_change_ignored_when_sel_high: assert property (
        @(posedge clk) (SEL && $stable(B) && $changed(SEL)) |-> $stable(Y)
    );

endmodule