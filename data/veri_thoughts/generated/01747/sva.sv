module signal_converter_sva (
    input logic clk,
    input logic [3:0] input_signal,
    input logic [2:0] output_signal
);

    ///// Functional mapping checks /////
    // For input <= 4, output equals (input - 1) truncated to 3 bits.
    check_low_range_function: assert property (
        @(posedge clk) disable iff (1'b0)
            (input_signal <= 4'd4) |-> (output_signal == ((input_signal - 4'd1) & 3'b111))
    );

    // For input > 4, output equals (input + 1) truncated to 3 bits.
    check_high_range_function: assert property (
        @(posedge clk) disable iff (1'b0)
            (input_signal > 4'd4) |-> (output_signal == ((input_signal + 4'd1) & 3'b111))
    );

    // For 1..4, decrement occurs without 3-bit wrap.
    check_decrement_no_wrap_1_to_4: assert property (
        @(posedge clk) disable iff (1'b0)
            (input_signal inside {[4'd1:4'd4]}) |-> (output_signal == (input_signal - 4'd1))
    );

    // For 5..6, increment occurs without 3-bit wrap.
    check_increment_no_wrap_5_to_6: assert property (
        @(posedge clk) disable iff (1'b0)
            (input_signal inside {[4'd5:4'd6]}) |-> (output_signal == (input_signal + 4'd1))
    );

    ///// Corner cases /////
    // Input 0 maps to 7 (wrap due to subtraction).
    check_zero_maps_to_7: assert property (
        @(posedge clk) disable iff (1'b0)
            (input_signal == 4'd0) |-> (output_signal == 3'd7)
    );

    // Input 4 maps to 3 (no wrap).
    check_four_maps_to_3: assert property (
        @(posedge clk) disable iff (1'b0)
            (input_signal == 4'd4) |-> (output_signal == 3'd3)
    );

    // Input 7 maps to 0 (wrap on increment).
    check_seven_maps_to_0: assert property (
        @(posedge clk) disable iff (1'b0)
            (input_signal == 4'd7) |-> (output_signal == 3'd0)
    );

    // Input 8 maps to 1 (post-wrap increment).
    check_eight_maps_to_1: assert property (
        @(posedge clk) disable iff (1'b0)
            (input_signal == 4'd8) |-> (output_signal == 3'd1)
    );

    // Input 15 maps to 0 (wrap due to increment).
    check_fifteen_maps_to_0: assert property (
        @(posedge clk) disable iff (1'b0)
            (input_signal == 4'd15) |-> (output_signal == 3'd0)
    );

endmodule