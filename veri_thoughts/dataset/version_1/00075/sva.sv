module mux6_sva #(parameter WIREWIDTH = 1) (
    input logic clk,
    input logic [2:0] s,
    input logic [WIREWIDTH:0] d0,
    input logic [WIREWIDTH:0] d1,
    input logic [WIREWIDTH:0] d2,
    input logic [WIREWIDTH:0] d3,
    input logic [WIREWIDTH:0] d4,
    input logic [WIREWIDTH:0] d5,
    input logic [WIREWIDTH:0] o
);

    // Select 0 routes d0 to o.
    check_sel_0_routes_d0: assert property (
        @(posedge clk) (s === 3'd0) |-> (o === d0)
    );

    // Select 1 routes d1 to o.
    check_sel_1_routes_d1: assert property (
        @(posedge clk) (s === 3'd1) |-> (o === d1)
    );

    // Select 2 routes d2 to o.
    check_sel_2_routes_d2: assert property (
        @(posedge clk) (s === 3'd2) |-> (o === d2)
    );

    // Select 3 routes d3 to o.
    check_sel_3_routes_d3: assert property (
        @(posedge clk) (s === 3'd3) |-> (o === d3)
    );

    // Select 4 routes d4 to o.
    check_sel_4_routes_d4: assert property (
        @(posedge clk) (s === 3'd4) |-> (o === d4)
    );

    // Select 5 uses the default path and routes d5 to o.
    check_sel_5_routes_d5: assert property (
        @(posedge clk) (s === 3'd5) |-> (o === d5)
    );

    // Select 6 uses the default path and routes d5 to o.
    check_sel_6_routes_d5: assert property (
        @(posedge clk) (s === 3'd6) |-> (o === d5)
    );

    // Select 7 uses the default path and routes d5 to o.
    check_sel_7_routes_d5: assert property (
        @(posedge clk) (s === 3'd7) |-> (o === d5)
    );

    // If all inputs are stable, o remains stable.
    check_output_stable_when_inputs_stable: assert property (
        @(posedge clk) $stable({s, d0, d1, d2, d3, d4, d5}) |-> $stable(o)
    );

    // Stable select and stable selected data keep o stable.
    check_unselected_inputs_do_not_affect_output: assert property (
        @(posedge clk)
        (
            ((s === 3'd0) && $stable(s) && $stable(d0)) ||
            ((s === 3'd1) && $stable(s) && $stable(d1)) ||
            ((s === 3'd2) && $stable(s) && $stable(d2)) ||
            ((s === 3'd3) && $stable(s) && $stable(d3)) ||
            ((s === 3'd4) && $stable(s) && $stable(d4)) ||
            ((s === 3'd5) && $stable(s) && $stable(d5)) ||
            ((s === 3'd6) && $stable(s) && $stable(d5)) ||
            ((s === 3'd7) && $stable(s) && $stable(d5))
        ) |-> $stable(o)
    );

endmodule