module top_module_sva (
    input logic clk,
    input logic reset,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic CIN,
    input logic [15:0] in,
    input logic [3:0] S,
    input logic [3:0] adder_out,
    input logic zero_to_one_out
);

    // Internal adder output matches A + B + CIN.
    check_adder_out_matches_inputs: assert property (
        @(posedge clk) disable iff (reset)
        adder_out == (A + B + CIN)
    );

    // Top output is the adder result plus the counter bit.
    check_s_matches_adder_plus_counter: assert property (
        @(posedge clk) disable iff (reset)
        S == (adder_out + zero_to_one_out)
    );

    // Reset clears the counter bit on the next cycle.
    check_counter_resets_low: assert property (
        @(posedge clk)
        reset |=> (zero_to_one_out == 1'b0)
    );

    // An all-ones input sets the counter bit on the next cycle.
    check_counter_sets_on_all_ones: assert property (
        @(posedge clk) disable iff (reset)
        (in == 16'hFFFF) |=> (zero_to_one_out == 1'b1)
    );

    // A non-FFFF input toggles the counter bit from 0 to 1.
    check_counter_toggle_low_to_high: assert property (
        @(posedge clk) disable iff (reset)
        ((in != 16'hFFFF) && (zero_to_one_out == 1'b0)) |=> (zero_to_one_out == 1'b1)
    );

    // A non-FFFF input toggles the counter bit from 1 to 0.
    check_counter_toggle_high_to_low: assert property (
        @(posedge clk) disable iff (reset)
        ((in != 16'hFFFF) && (zero_to_one_out == 1'b1)) |=> (zero_to_one_out == 1'b0)
    );

    // After reset, the output reduces to the plain adder result.
    check_output_after_reset_is_plain_sum: assert property (
        @(posedge clk)
        reset |=> (S == (A + B + CIN))
    );

    // After an all-ones input, the output includes the extra one.
    check_output_after_all_ones_has_extra_one: assert property (
        @(posedge clk) disable iff (reset)
        (in == 16'hFFFF) |=> (S == (A + B + CIN + 1'b1))
    );

    // With a non-FFFF input and counter bit low, the next output adds one.
    check_output_toggle_low_to_high: assert property (
        @(posedge clk) disable iff (reset)
        ((in != 16'hFFFF) && (zero_to_one_out == 1'b0)) |=> (S == (A + B + CIN + 1'b1))
    );

    // With a non-FFFF input and counter bit high, the next output drops the extra one.
    check_output_toggle_high_to_low: assert property (
        @(posedge clk) disable iff (reset)
        ((in != 16'hFFFF) && (zero_to_one_out == 1'b1)) |=> (S == (A + B + CIN))
    );

endmodule