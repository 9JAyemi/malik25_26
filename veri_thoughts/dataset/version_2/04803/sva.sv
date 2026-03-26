module mux_2to1_sva (
    input logic clk,
    input logic in1,
    input logic in2,
    input logic select,
    input logic out
);

    // The output must always match the mux expression.
    check_mux_function: assert property (
        @(posedge clk) out === (select ? in2 : in1)
    );

    // When select is low, the output must match in1.
    check_select_low_routes_in1: assert property (
        @(posedge clk) (select === 1'b0) |-> (out === in1)
    );

    // When select is high, the output must match in2.
    check_select_high_routes_in2: assert property (
        @(posedge clk) (select === 1'b1) |-> (out === in2)
    );

endmodule