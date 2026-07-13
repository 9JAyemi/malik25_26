module mux_2to1_sva (
    input logic clk,
    input logic a,
    input logic b,
    input logic sel,
    input logic out
);

    // When sel is low, the mux passes a.
    check_select_a_path: assert property (
        @(posedge clk) !sel |-> (out == a)
    );

    // When sel is high, the mux passes b.
    check_select_b_path: assert property (
        @(posedge clk) sel |-> (out == b)
    );

    // Output always matches the mux equation.
    check_mux_equation: assert property (
        @(posedge clk) (out == (sel ? b : a))
    );

    // If both inputs are equal, output matches that value.
    check_equal_inputs_consistency: assert property (
        @(posedge clk) (a == b) |-> (out == a)
    );

endmodule