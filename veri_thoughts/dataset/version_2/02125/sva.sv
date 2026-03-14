module consecutive_ones_sva (
    input logic clk,
    input logic [15:0] input_signal,
    input logic [3:0] output_signal
);
    // Clock: clk (posedge). No reset in RTL.
    // Sequential logic: count registered each clk; output_signal = count.
    // Behavior: output is 0..4 based on input; special cases 16'h0000 -> 0, 16'hFFFF -> 4; else based on input[3:0] consecutive 1s ending at bit 3.

    // Output value is always within 0..4 on the next cycle.
    check_output_range_0_to_4: assert property (
        @(posedge clk) 1'b1 |=> (output_signal inside {4'h0,4'h1,4'h2,4'h3,4'h4})
    );

    // All-zero input drives 0 next cycle.
    check_all_zero_maps_to_zero: assert property (
        @(posedge clk) (input_signal == 16'h0000) |=> (output_signal == 4'h0)
    );

    // All-one 16-bit input drives 4 next cycle.
    check_all_ones16_maps_to_four: assert property (
        @(posedge clk) (input_signal == 16'hFFFF) |=> (output_signal == 4'h4)
    );

    // Lower nibble 1111 drives 4 next cycle.
    check_lower_nibble_1111_maps_to_four: assert property (
        @(posedge clk) (input_signal[3:0] == 4'hF) |=> (output_signal == 4'h4)
    );

    // Lower nibble 1110 drives 3 next cycle.
    check_lower_nibble_1110_maps_to_three: assert property (
        @(posedge clk) ((input_signal[3:1] == 3'b111) && (input_signal[0] == 1'b0)) |=> (output_signal == 4'h3)
    );

    // Lower nibble 11x? with b1==0 (i.e., b3=1,b2=1,b1=0) drives 2 next cycle.
    check_lower_nibble_110x_b1_0_maps_to_two: assert property (
        @(posedge clk) ((input_signal[3:2] == 2'b11) && (input_signal[1] == 1'b0)) |=> (output_signal == 4'h2)
    );

    // Lower nibble 10xx (b3=1,b2=0) drives 1 next cycle.
    check_lower_nibble_10xx_maps_to_one: assert property (
        @(posedge clk) ((input_signal[3] == 1'b1) && (input_signal[2] == 1'b0)) |=> (output_signal == 4'h1)
    );

    // If b3 is 0, output is 0 next cycle.
    check_b3_zero_maps_to_zero: assert property (
        @(posedge clk) (input_signal[3] == 1'b0) |=> (output_signal == 4'h0)
    );

    // If input is unchanged across cycles, output is unchanged on the next cycle.
    check_stateless_mapping_stability: assert property (
        @(posedge clk) (input_signal == $past(input_signal)) |=> (output_signal == $past(output_signal))
    );

endmodule