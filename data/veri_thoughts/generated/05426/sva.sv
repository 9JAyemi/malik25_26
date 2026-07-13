module add_one_and_concat_sva (
    input logic        clk,
    input logic [31:0] input_signal,
    input logic [15:0] output_signal
);

    // Output is always the low 16 bits of the input plus one.
    check_output_matches_low_half_plus_one: assert property (
        @(posedge clk) output_signal == (input_signal[15:0] + 16'd1)
    );

    // A max low-half value wraps the 16-bit output to zero.
    check_wraps_on_low_half_overflow: assert property (
        @(posedge clk) (input_signal[15:0] == 16'hFFFF) |-> (output_signal == 16'h0000)
    );

    // Without overflow, the output is one greater than the low half.
    check_increments_without_wrap: assert property (
        @(posedge clk)
        (input_signal[15:0] != 16'hFFFF)
        |-> ((output_signal == (input_signal[15:0] + 16'd1)) &&
             (output_signal > input_signal[15:0]))
    );

    // If the low 16 bits stay the same, the output stays the same.
    check_output_stable_when_low_half_stable: assert property (
        @(posedge clk)
        (!$initstate && (input_signal[15:0] == $past(input_signal[15:0])))
        |-> (output_signal == $past(output_signal))
    );

    // If the low 16 bits change, the output also changes.
    check_output_changes_when_low_half_changes: assert property (
        @(posedge clk)
        (!$initstate && (input_signal[15:0] != $past(input_signal[15:0])))
        |-> (output_signal != $past(output_signal))
    );

endmodule