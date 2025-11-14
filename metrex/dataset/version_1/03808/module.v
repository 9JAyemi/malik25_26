
module signal_combiner (
    input [3:0] input_signals,
    output output_signal
);

wire[1:0] input_sum;

assign input_sum[0] = input_signals[0] ^ input_signals[1];
assign input_sum[1] = input_signals[2] ^ input_signals[3];

assign output_signal = input_sum[0] ^ input_sum[1];

endmodule