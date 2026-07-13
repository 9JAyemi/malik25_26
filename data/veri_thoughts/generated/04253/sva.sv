module ADC_INTERFACE_sva (
    input logic clk,
    input logic reset_n,
    input logic [11:0] adc_data,
    input logic valid,
    input logic [15:0] data_out
);

    // Active-low reset clears both outputs.
    check_reset_clears_outputs: assert property (
        @(posedge clk) !reset_n |-> (valid == 1'b0 && data_out == 16'h0000)
    );

    // A nonzero ADC sample sets valid on the next clock sample.
    check_nonzero_input_sets_valid: assert property (
        @(posedge clk) disable iff (!reset_n)
        (adc_data != 12'h000) |=> (valid == 1'b1)
    );

    // A nonzero ADC sample is zero-extended into data_out.
    check_nonzero_input_updates_data_out: assert property (
        @(posedge clk) disable iff (!reset_n)
        (adc_data != 12'h000) |=> (data_out == {4'b0000, $past(adc_data)})
    );

    // A zero ADC sample leaves valid unchanged.
    check_zero_input_holds_valid: assert property (
        @(posedge clk) disable iff (!reset_n)
        (adc_data == 12'h000) |=> (valid == $past(valid))
    );

    // A zero ADC sample leaves data_out unchanged.
    check_zero_input_holds_data_out: assert property (
        @(posedge clk) disable iff (!reset_n)
        (adc_data == 12'h000) |=> (data_out == $past(data_out))
    );

    // Once valid is high, it stays high until reset.
    check_valid_is_sticky: assert property (
        @(posedge clk) disable iff (!reset_n)
        valid |=> valid
    );

endmodule