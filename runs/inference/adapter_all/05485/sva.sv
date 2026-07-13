module mux2to1_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic SEL,
    input logic Y
);

    // When SEL is 0, Y must equal A.
    check_sel0_routes_a: assert property (
        @(posedge clk) (SEL === 1'b0) |-> (Y === A)
    );

    // When SEL is 1, Y must equal B.
    check_sel1_routes_b: assert property (
        @(posedge clk) (SEL === 1'b1) |-> (Y === B)
    );

    // When SEL is unknown, Y must be unknown.
    check_unknown_sel_gives_unknown_y: assert property (
        @(posedge clk) (SEL !== 1'b0 && SEL !== 1'b1) |-> (Y === 1'bx)
    );

    // With SEL held at 0 and A stable, Y must remain stable.
    check_sel0_stable_keeps_y_stable: assert property (
        @(posedge clk) (SEL === 1'b0 && $stable(SEL) && $stable(A)) |-> $stable(Y)
    );

    // With SEL held at 1 and B stable, Y must remain stable.
    check_sel1_stable_keeps_y_stable: assert property (
        @(posedge clk) (SEL === 1'b1 && $stable(SEL) && $stable(B)) |-> $stable(Y)
    );

    // With SEL held at 0 and A changing, Y must change.
    check_sel0_change_propagates_to_y: assert property (
        @(posedge clk) (SEL === 1'b0 && $stable(SEL) && $changed(A)) |-> $changed(Y)
    );

    // With SEL held at 1 and B changing, Y must change.
    check_sel1_change_propagates_to_y: assert property (
        @(posedge clk) (SEL === 1'b1 && $stable(SEL) && $changed(B)) |-> $changed(Y)
    );

endmodule