module mux_2to1_assertions (
    input logic clk,
    input logic A,
    input logic B,
    input logic SEL,
    input logic OUT
);

    // OUT always matches the mux select function.
    check_mux_function: assert property (
        @(posedge clk) OUT == ((SEL == 1'b0) ? A : B)
    );

    // When SEL is low, OUT routes A.
    check_sel_zero_routes_a: assert property (
        @(posedge clk) (SEL == 1'b0) |-> (OUT == A)
    );

    // When SEL is high, OUT routes B.
    check_sel_one_routes_b: assert property (
        @(posedge clk) (SEL == 1'b1) |-> (OUT == B)
    );

    // A rising SEL causes OUT to select B.
    check_sel_rise_selects_b: assert property (
        @(posedge clk) $rose(SEL) |-> (OUT == B)
    );

    // A falling SEL causes OUT to select A.
    check_sel_fall_selects_a: assert property (
        @(posedge clk) $fell(SEL) |-> (OUT == A)
    );

    // B does not affect OUT while SEL stays low and A is stable.
    check_b_ignored_when_sel_zero: assert property (
        @(posedge clk) ($stable(SEL) && (SEL == 1'b0) && $stable(A) && $changed(B)) |-> $stable(OUT)
    );

    // A does not affect OUT while SEL stays high and B is stable.
    check_a_ignored_when_sel_one: assert property (
        @(posedge clk) ($stable(SEL) && (SEL == 1'b1) && $stable(B) && $changed(A)) |-> $stable(OUT)
    );

endmodule