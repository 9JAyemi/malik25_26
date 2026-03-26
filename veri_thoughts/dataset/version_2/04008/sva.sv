module top_module_sva (
    input logic       clk,
    input logic       reset,
    input logic [7:0] d,
    input logic [7:0] in,
    input logic [7:0] q
);

    // clk is the only clock; reset is active-high and synchronous.

    // q matches the previously stored value masked by the current input.
    check_sampled_top_function: assert property (
        @(posedge clk) disable iff ($initstate)
        q == ((($past(reset)) ? 8'h00 : $past(d)) & in)
    );

    // A reset cycle clears the stored value, so q is zero on the next sample.
    check_reset_clears_output_next: assert property (
        @(posedge clk) reset |=> (q == 8'h00)
    );

    // q can only contain bits enabled by the current input mask.
    check_output_masked_by_input: assert property (
        @(posedge clk) disable iff (reset)
        ((q & ~in) == 8'h00)
    );

    // A zero mask forces q low.
    check_zero_mask_forces_zero_output: assert property (
        @(posedge clk) disable iff (reset)
        (in == 8'h00) |-> (q == 8'h00)
    );

    // Capturing zero data forces q low on the next sample.
    check_zero_data_clears_next_output: assert property (
        @(posedge clk) (!reset && (d == 8'h00)) |=> (q == 8'h00)
    );

    // Capturing all ones makes q mirror the current input on the next sample.
    check_all_ones_data_passes_input_next: assert property (
        @(posedge clk) (!reset && (d == 8'hFF)) |=> (q == in)
    );

    // With an all-ones mask, q exposes the previously captured data.
    check_all_ones_mask_reveals_previous_data: assert property (
        @(posedge clk) disable iff ($initstate)
        ((!$past(reset)) && (in == 8'hFF)) |-> (q == $past(d))
    );

endmodule