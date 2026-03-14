module top_module_sva (
    input logic clk,
    input logic reset,            // Synchronous active-high reset
    input logic [2:0] select1,
    input logic [2:0] select2,
    input logic out,
    // Internal signals from top_module
    input logic [3:0] counter,
    input logic [3:0] counter_output,
    input logic [2:0] decoder_input,
    input logic [7:0] decoder_output
);
    ///// Wiring and decoder behavior /////
    // decoder_input is directly driven by select2.
    connect_decoder_input_to_select2: assert property (
        @(posedge clk) disable iff (reset) decoder_input == select2
    );
    // Decoder output is one-hot for all inputs.
    decoder_onehot_output: assert property (
        @(posedge clk) disable iff (reset) $onehot(decoder_output)
    );
    // The bit indexed by decoder_input is HIGH.
    decoder_selected_bit_is_one: assert property (
        @(posedge clk) disable iff (reset) decoder_output[decoder_input] == 1'b1
    );
    // Decoder equals 1 shifted left by decoder_input.
    decoder_matches_shift: assert property (
        @(posedge clk) disable iff (reset) decoder_output == (8'b0000_0001 << decoder_input)
    );
    // The bit selected by select1 equals (select1 == decoder_input).
    decoder_selected_bit_matches_index: assert property (
        @(posedge clk) disable iff (reset) decoder_output[select1] == (select1 == decoder_input)
    );

    ///// Counter instance behavior (counter_inst.out -> counter_output) /////
    // On reset, counter_output clears to 0.
    counter_inst_reset_clears: assert property (
        @(posedge clk) reset |-> (counter_output == 4'b0000)
    );
    // When not in reset for two consecutive cycles, counter_output increments by 1.
    counter_inst_increments: assert property (
        @(posedge clk) disable iff (reset) (!reset && !$past(reset)) |-> (counter_output == $past(counter_output) + 4'd1)
    );

    ///// Local counter reg behavior (top_module.counter) /////
    // On reset, local counter clears to 0.
    local_counter_reset_clears: assert property (
        @(posedge clk) reset |-> (counter == 4'b0000)
    );
    // When not in reset for two consecutive cycles, local counter increments by 1.
    local_counter_increments: assert property (
        @(posedge clk) disable iff (reset) (!reset && !$past(reset)) |-> (counter == $past(counter) + 4'd1)
    );

    ///// Output selection logic /////
    // out equals AND of counter_output[select2] and decoder_output[select1].
    out_equals_and_of_selecteds: assert property (
        @(posedge clk) disable iff (reset) out == (counter_output[select2] & decoder_output[select1])
    );
    // If selected decoder bit is 0, out must be 0.
    out_zero_when_decoder_bit_zero: assert property (
        @(posedge clk) disable iff (reset) (decoder_output[select1] == 1'b0) |-> (out == 1'b0)
    );
    // If selected decoder bit is 1, out equals the selected counter bit.
    out_equals_counterbit_when_decoder_bit_one: assert property (
        @(posedge clk) disable iff (reset) (decoder_output[select1] == 1'b1) |-> (out == counter_output[select2])
    );
    // During reset, out must be 0 (counter_output is held at 0).
    out_is_zero_during_reset: assert property (
        @(posedge clk) reset |-> (out == 1'b0)
    );
endmodule