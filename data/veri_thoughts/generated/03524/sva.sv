module mux_4to1_sva (
    input logic clk,
    input logic in0,
    input logic in1,
    input logic in2,
    input logic in3,
    input logic sel1,
    input logic sel0,
    input logic out
);

    // Output matches the RTL sum-of-products implementation.
    check_mux_sum_of_products: assert property (
        @(posedge clk)
        out == ((in0 & ~sel1 & ~sel0) |
                (in1 & ~sel1 &  sel0) |
                (in2 &  sel1 & ~sel0) |
                (in3 &  sel1 &  sel0))
    );

    // Select 00 routes in0 to the output.
    check_select_00_routes_in0: assert property (
        @(posedge clk)
        (!sel1 && !sel0) |-> (out == in0)
    );

    // Select 01 routes in1 to the output.
    check_select_01_routes_in1: assert property (
        @(posedge clk)
        (!sel1 && sel0) |-> (out == in1)
    );

    // Select 10 routes in2 to the output.
    check_select_10_routes_in2: assert property (
        @(posedge clk)
        (sel1 && !sel0) |-> (out == in2)
    );

    // Select 11 routes in3 to the output.
    check_select_11_routes_in3: assert property (
        @(posedge clk)
        (sel1 && sel0) |-> (out == in3)
    );

    // If all inputs and selects are stable, the output remains stable.
    check_stable_inputs_keep_output_stable: assert property (
        @(posedge clk)
        (!$initstate && $stable({in0, in1, in2, in3, sel1, sel0})) |-> $stable(out)
    );

endmodule