module mux_2to1_sva (
    input logic clk,
    input logic a,
    input logic b,
    input logic sel,
    input logic y
);

    // Output must match the RTL mux expression.
    check_mux_function: assert property (
        @(posedge clk) y === ((sel == 1'b0) ? a : b)
    );

    // Low select routes a to y.
    check_select_low_routes_a: assert property (
        @(posedge clk) (sel === 1'b0) |-> (y === a)
    );

    // High select routes b to y.
    check_select_high_routes_b: assert property (
        @(posedge clk) (sel === 1'b1) |-> (y === b)
    );

    // Equal inputs force the same output regardless of select.
    check_equal_inputs_same_output: assert property (
        @(posedge clk) (a === b) |-> (y === a)
    );

    // With low select and stable a, y must remain stable.
    check_b_ignored_when_select_low: assert property (
        @(posedge clk) (($past(sel) === 1'b0) && (sel === 1'b0) && $stable(a)) |-> (y === $past(y))
    );

    // With high select and stable b, y must remain stable.
    check_a_ignored_when_select_high: assert property (
        @(posedge clk) (($past(sel) === 1'b1) && (sel === 1'b1) && $stable(b)) |-> (y === $past(y))
    );

endmodule