module mux_2to1_sva (
    input logic clk,
    input logic a,
    input logic b,
    input logic sel,
    input logic out
);

    // Output must match the mux select expression.
    check_mux_function: assert property (
        @(posedge clk) out == ((sel == 1'b1) ? b : a)
    );

    // When select is low, output must follow input a.
    check_select_low_routes_a: assert property (
        @(posedge clk) (sel == 1'b0) |-> (out == a)
    );

    // When select is high, output must follow input b.
    check_select_high_routes_b: assert property (
        @(posedge clk) (sel == 1'b1) |-> (out == b)
    );

    // If both inputs are equal, output must match that common value.
    check_equal_inputs_passthrough: assert property (
        @(posedge clk) (a == b) |-> (out == a)
    );

endmodule