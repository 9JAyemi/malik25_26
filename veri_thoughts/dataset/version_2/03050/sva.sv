module mux_2_to_1_sva (
    input logic clk,
    input logic data_in_0,
    input logic data_in_1,
    input logic select,
    input logic data_out
);

    // Output must implement the 2:1 mux expression.
    check_mux_function: assert property (
        @(posedge clk) data_out == (select ? data_in_1 : data_in_0)
    );

    // When select is low, output must follow data_in_0.
    check_select_low_path: assert property (
        @(posedge clk) !select |-> (data_out == data_in_0)
    );

    // When select is high, output must follow data_in_1.
    check_select_high_path: assert property (
        @(posedge clk) select |-> (data_out == data_in_1)
    );

    // If both inputs are equal, output must equal that shared value.
    check_equal_inputs_consistent_output: assert property (
        @(posedge clk) (data_in_0 == data_in_1) |-> (data_out == data_in_0)
    );

endmodule