module mux2to1_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic SEL,
    input logic X
);

    // X must equal the selected input.
    check_mux_function: assert property (
        @(posedge clk) X == (SEL ? B : A)
    );

    // SEL low must route A to X.
    check_sel_low_routes_a: assert property (
        @(posedge clk) !SEL |-> (X == A)
    );

    // SEL high must route B to X.
    check_sel_high_routes_b: assert property (
        @(posedge clk) SEL |-> (X == B)
    );

    // Equal inputs must pass through regardless of SEL.
    check_equal_inputs_passthrough: assert property (
        @(posedge clk) (A == B) |-> (X == A)
    );

    // A=0 and B=1 makes X follow SEL.
    check_01_case: assert property (
        @(posedge clk) (!A && B) |-> (X == SEL)
    );

    // A=1 and B=0 makes X follow inverted SEL.
    check_10_case: assert property (
        @(posedge clk) (A && !B) |-> (X == ~SEL)
    );

endmodule