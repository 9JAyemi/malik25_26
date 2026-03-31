module mux_2to1_sva (
    input logic clk, // sampling clock for assertions
    input logic a,
    input logic b,
    input logic sel,
    input logic y
);

    // RTL has no reset; all checks are sampled on clk.

    // y must match the implemented mux equation.
    check_mux_equation: assert property (
        @(posedge clk) y == ((a & ~sel) | (b & sel))
    );

    // When sel is low, y follows a.
    check_sel_low_routes_a: assert property (
        @(posedge clk) (sel == 1'b0) |-> (y == a)
    );

    // When sel is high, y follows b.
    check_sel_high_routes_b: assert property (
        @(posedge clk) (sel == 1'b1) |-> (y == b)
    );

    // If both inputs are low, y is low.
    check_both_inputs_low: assert property (
        @(posedge clk) ((a == 1'b0) && (b == 1'b0)) |-> (y == 1'b0)
    );

    // If both inputs are high, y is high.
    check_both_inputs_high: assert property (
        @(posedge clk) ((a == 1'b1) && (b == 1'b1)) |-> (y == 1'b1)
    );

endmodule