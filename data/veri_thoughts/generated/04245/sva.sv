module pipeline_register_assertions (
    input logic clk,
    input logic reset,
    input logic [31:0] data_in,
    input logic [31:0] data_out
);

    // On consecutive non-reset cycles, output matches the prior cycle's input.
    check_capture_previous_input: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (data_out == $past(data_in))
    );

    // After reset is released, the observed output remains cleared.
    check_output_zero_after_reset_release: assert property (
        @(posedge clk) disable iff (reset)
        (!$initstate && $past(reset)) |-> (data_out == 32'h00000000)
    );

    // If the prior input already matched the prior output, the output holds.
    check_hold_when_input_matches_previous_output: assert property (
        @(posedge clk) disable iff (reset)
        (!$initstate && !$past(reset) && ($past(data_in) == $past(data_out))) |-> (data_out == $past(data_out))
    );

    // If the prior input differed from the prior output, the output updates.
    check_update_when_input_differs_from_previous_output: assert property (
        @(posedge clk) disable iff (reset)
        (!$initstate && !$past(reset) && ($past(data_in) != $past(data_out))) |-> (data_out != $past(data_out))
    );

endmodule