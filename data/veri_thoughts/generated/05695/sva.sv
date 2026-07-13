module mux4x1_sva (
    input logic clk,
    input logic a,
    input logic b,
    input logic c,
    input logic d,
    input logic sel0,
    input logic sel1,
    input logic y
);

    // y always matches the selected 4:1 mux input.
    check_output_matches_selected_input: assert property (
        @(posedge clk)
        y == (sel1 ? (sel0 ? d : c) : (sel0 ? b : a))
    );

    // When sel1 is low, y selects between a and b using sel0.
    check_sel1_low_uses_ab_pair: assert property (
        @(posedge clk)
        !sel1 |-> (y == (sel0 ? b : a))
    );

    // When sel1 is high, y selects between c and d using sel0.
    check_sel1_high_uses_cd_pair: assert property (
        @(posedge clk)
        sel1 |-> (y == (sel0 ? d : c))
    );

    // Select code 2'b00 routes a to y.
    check_sel_00_routes_a: assert property (
        @(posedge clk)
        (!sel1 && !sel0) |-> (y == a)
    );

    // Select code 2'b01 routes b to y.
    check_sel_01_routes_b: assert property (
        @(posedge clk)
        (!sel1 && sel0) |-> (y == b)
    );

    // Select code 2'b10 routes c to y.
    check_sel_10_routes_c: assert property (
        @(posedge clk)
        (sel1 && !sel0) |-> (y == c)
    );

    // Select code 2'b11 routes d to y.
    check_sel_11_routes_d: assert property (
        @(posedge clk)
        (sel1 && sel0) |-> (y == d)
    );

endmodule