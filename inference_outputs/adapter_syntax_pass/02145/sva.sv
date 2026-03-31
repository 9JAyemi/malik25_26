module mux_2_to_1_sva (
    input logic clk,
    input logic a,
    input logic b,
    input logic sel,
    input logic out
);

    // When sel is low, out must equal a.
    check_sel_low_routes_a: assert property (
        @(posedge clk) (sel === 1'b0) |-> (out === a)
    );

    // When sel is high, out must equal b.
    check_sel_high_routes_b: assert property (
        @(posedge clk) (sel === 1'b1) |-> (out === b)
    );

    // If both inputs are equal, out must match that common value.
    check_equal_inputs_passthrough: assert property (
        @(posedge clk) (a === b) |-> (out === a)
    );

endmodule