module mux_2to1_sva (
    input logic clk,
    input logic a,
    input logic b,
    input logic sel,
    input logic y
);

// y must match the RTL's combinational equation.
    check_function_equivalence: assert property (
        @(posedge clk) y == ((~sel & a) | (sel & b))
    );

// When sel is low, y must follow a.
    check_sel_low_routes_a: assert property (
        @(posedge clk) !sel |-> (y == a)
    );

// When sel is high, y must follow b.
    check_sel_high_routes_b: assert property (
        @(posedge clk) sel |-> (y == b)
    );

// A high output requires at least one high data input.
    check_y_high_requires_data_high: assert property (
        @(posedge clk) y |-> (a || b)
    );

// A low output requires both data inputs to be low.
    check_y_low_requires_data_low: assert property (
        @(posedge clk) !y |-> (!a && !b)
    );

endmodule
