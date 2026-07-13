module data_converter_sva (
    input logic       clk,
    input logic [3:0] data_in,
    input logic [1:0] data_out
);

    // Output must match the RTL threshold expression.
    check_output_equation: assert property (
        @(posedge clk)
        data_out == (
            (data_in <= 4'd4)  ? 2'b00 :
            (data_in <= 4'd8)  ? 2'b01 :
            (data_in <= 4'd12) ? 2'b10 : 2'b11
        )
    );

    // Inputs 0 through 4 must map to 2'b00.
    check_range_0_to_4: assert property (
        @(posedge clk)
        (data_in <= 4'd4) |-> (data_out == 2'b00)
    );

    // Inputs 5 through 8 must map to 2'b01.
    check_range_5_to_8: assert property (
        @(posedge clk)
        ((data_in >= 4'd5) && (data_in <= 4'd8)) |-> (data_out == 2'b01)
    );

    // Inputs 9 through 12 must map to 2'b10.
    check_range_9_to_12: assert property (
        @(posedge clk)
        ((data_in >= 4'd9) && (data_in <= 4'd12)) |-> (data_out == 2'b10)
    );

    // Inputs 13 through 15 must map to 2'b11.
    check_range_13_to_15: assert property (
        @(posedge clk)
        (data_in >= 4'd13) |-> (data_out == 2'b11)
    );

    // The lower threshold value 4 must produce 2'b00.
    check_threshold_at_4: assert property (
        @(posedge clk)
        (data_in == 4'd4) |-> (data_out == 2'b00)
    );

    // The next value after 4 must produce 2'b01.
    check_threshold_at_5: assert property (
        @(posedge clk)
        (data_in == 4'd5) |-> (data_out == 2'b01)
    );

    // The upper value of the second range must produce 2'b01.
    check_threshold_at_8: assert property (
        @(posedge clk)
        (data_in == 4'd8) |-> (data_out == 2'b01)
    );

    // The next value after 8 must produce 2'b10.
    check_threshold_at_9: assert property (
        @(posedge clk)
        (data_in == 4'd9) |-> (data_out == 2'b10)
    );

    // The upper value of the third range must produce 2'b10.
    check_threshold_at_12: assert property (
        @(posedge clk)
        (data_in == 4'd12) |-> (data_out == 2'b10)
    );

    // The next value after 12 must produce 2'b11.
    check_threshold_at_13: assert property (
        @(posedge clk)
        (data_in == 4'd13) |-> (data_out == 2'b11)
    );

endmodule