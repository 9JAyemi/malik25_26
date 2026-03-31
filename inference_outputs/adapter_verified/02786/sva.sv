module mux_2_1_sva (
    input logic clk,
    input logic a,
    input logic b,
    input logic sel,
    input logic out
);

// When sel is 0, out must equal a.
    check_sel0_routes_a: assert property (
        @(posedge clk) (sel == 1'b0) |-> (out == a)
    );

// When sel is 1, out must equal b.
    check_sel1_routes_b: assert property (
        @(posedge clk) (sel == 1'b1) |-> (out == b)
    );

// When a and b are equal, out must equal that value regardless of sel.
    check_equal_inputs_passthrough: assert property (
        @(posedge clk) (a == b) |-> (out == a)
    );

// If a and b differ and sel is 0, out must differ from b.
    check_sel0_differs_from_b: assert property (
        @(posedge clk) (a != b && sel == 1'b0) |-> (out != b)
    );

// If a and b differ and sel is 1, out must differ from a.
    check_sel1_differs_from_a: assert property (
        @(posedge clk) (a != b && sel == 1'b1) |-> (out != a)
    );

endmodule
