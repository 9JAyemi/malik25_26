module mux_2to1_sva (
    input logic clk,
    input logic a,
    input logic b,
    input logic sel,
    input logic y
);

    // y must match the implemented mux equation.
    check_mux_equation: assert property (
        @(posedge clk) y == ((~sel & a) | (sel & b))
    );

    // When sel is low, y must follow a.
    check_select_low_routes_a: assert property (
        @(posedge clk) (sel == 1'b0) |-> (y == a)
    );

    // When sel is high, y must follow b.
    check_select_high_routes_b: assert property (
        @(posedge clk) (sel == 1'b1) |-> (y == b)
    );

    // If both inputs are low, y must be low.
    check_both_inputs_low: assert property (
        @(posedge clk) ((a == 1'b0) && (b == 1'b0)) |-> (y == 1'b0)
    );

    // If both inputs are high, y must be high.
    check_both_inputs_high: assert property (
        @(posedge clk) ((a == 1'b1) && (b == 1'b1)) |-> (y == 1'b1)
    );

    // If a is low and b is high, y must match sel.
    check_low_high_inputs: assert property (
        @(posedge clk) ((a == 1'b0) && (b == 1'b1)) |-> (y == sel)
    );

    // If a is high and b is low, y must match inverted sel.
    check_high_low_inputs: assert property (
        @(posedge clk) ((a == 1'b1) && (b == 1'b0)) |-> (y == ~sel)
    );

endmodule