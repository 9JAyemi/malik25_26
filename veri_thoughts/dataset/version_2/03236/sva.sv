module mux_2to1_enable_sva (
    input logic clk,
    input logic a,
    input logic b,
    input logic enable,
    input logic mux_out
);

    // When enable is high, the output follows input a.
    check_select_a: assert property (
        @(posedge clk) (enable === 1'b1) |-> (mux_out === a)
    );

    // When enable is not high, the output follows input b.
    check_select_b: assert property (
        @(posedge clk) (enable !== 1'b1) |-> (mux_out === b)
    );

    // When both inputs match, the output matches that common value.
    check_equal_inputs_common_value: assert property (
        @(posedge clk) (a === b) |-> (mux_out === a)
    );

endmodule