module top_module_sva (
    input logic        clk,
    input logic        reset,
    input logic [15:0] in,
    input logic [7:0]  final_output,
    input logic [7:0]  upper_byte,
    input logic [7:0]  lower_byte,
    input logic [7:0]  xor_output
);

    // Reset clears upper_byte on the following cycle.
    check_upper_byte_reset_zero: assert property (
        @(posedge clk) reset |=> (upper_byte == 8'h00)
    );

    // Reset clears lower_byte on the following cycle.
    check_lower_byte_reset_zero: assert property (
        @(posedge clk) reset |=> (lower_byte == 8'h00)
    );

    // Reset clears final_output on the following cycle.
    check_final_output_reset_zero: assert property (
        @(posedge clk) reset |=> (final_output == 8'h00)
    );

    // upper_byte captures the input upper byte after a non-reset cycle.
    check_upper_byte_captures_input: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        !$past(reset) |-> (upper_byte == $past(in[15:8]))
    );

    // lower_byte captures the input lower byte after a non-reset cycle.
    check_lower_byte_captures_input: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        !$past(reset) |-> (lower_byte == $past(in[7:0]))
    );

    // module2 output is the XOR of upper_byte and lower_byte.
    check_xor_output_matches_inputs: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        (xor_output == (upper_byte ^ lower_byte))
    );

    // final_output captures the prior-cycle xor_output XOR lower_byte.
    check_final_output_uses_prior_xor_and_lower: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        !$past(reset) |-> (final_output == ($past(xor_output) ^ $past(lower_byte)))
    );

    // final_output reduces to the prior-cycle upper_byte.
    check_final_output_equals_prior_upper_byte: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        !$past(reset) |-> (final_output == $past(upper_byte))
    );

endmodule