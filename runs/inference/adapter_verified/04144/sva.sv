module mux_2to1_sva (
    input logic clk,
    input logic a,
    input logic b,
    input logic sel,
    input logic out
);

// Output must match the RTL mux expression.
    check_mux_function: assert property (
        @(posedge clk) out == ((sel == 1'b1) ? b : a)
    );

// When select is low, output must follow input a.
    check_select_a: assert property (
        @(posedge clk) (sel == 1'b0) |-> (out == a)
    );

// When select is high, output must follow input b.
    check_select_b: assert property (
        @(posedge clk) (sel == 1'b1) |-> (out == b)
    );

// Equal inputs must force the same value on the output.
    check_equal_inputs: assert property (
        @(posedge clk) (a == b) |-> (out == a)
    );

endmodule
