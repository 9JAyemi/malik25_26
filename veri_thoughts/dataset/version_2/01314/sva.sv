module mux2to1_sva (
    input logic clk,
    input logic a,
    input logic b,
    input logic sel,
    input logic out
);
    // Core mux behavior: out equals a when sel=1 else b.
    check_mux_function: assert property (
        @(posedge clk) out == (sel ? a : b)
    );

    // When sel is 1, out must equal a.
    check_sel1_routes_a: assert property (
        @(posedge clk) sel |-> (out == a)
    );

    // When sel is 0, out must equal b.
    check_sel0_routes_b: assert property (
        @(posedge clk) !sel |-> (out == b)
    );

    // If a and b are equal, out must equal that value regardless of sel.
    check_equal_inputs_passthrough: assert property (
        @(posedge clk) (a == b) |-> (out == a)
    );
endmodule