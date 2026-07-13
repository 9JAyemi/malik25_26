module signal_processor_sva (
    input logic        clk,
    input logic [15:0] input_signal,
    input logic [1:0]  output_signal
);

    // Inputs below 1000 map to 01.
    check_low_range_encoding: assert property (
        @(posedge clk) (input_signal < 16'd1000) |-> (output_signal == 2'b01)
    );

    // Inputs from 1000 through 2000 map to 10.
    check_mid_range_encoding: assert property (
        @(posedge clk) ((input_signal >= 16'd1000) && (input_signal <= 16'd2000)) |-> (output_signal == 2'b10)
    );

    // Inputs above 2000 map to 11.
    check_high_range_encoding: assert property (
        @(posedge clk) (input_signal > 16'd2000) |-> (output_signal == 2'b11)
    );

    // Boundary value 999 stays in the low range.
    check_boundary_999: assert property (
        @(posedge clk) (input_signal == 16'd999) |-> (output_signal == 2'b01)
    );

    // Boundary value 1000 enters the middle range.
    check_boundary_1000: assert property (
        @(posedge clk) (input_signal == 16'd1000) |-> (output_signal == 2'b10)
    );

    // Boundary value 2000 remains in the middle range.
    check_boundary_2000: assert property (
        @(posedge clk) (input_signal == 16'd2000) |-> (output_signal == 2'b10)
    );

    // Boundary value 2001 enters the high range.
    check_boundary_2001: assert property (
        @(posedge clk) (input_signal == 16'd2001) |-> (output_signal == 2'b11)
    );

endmodule