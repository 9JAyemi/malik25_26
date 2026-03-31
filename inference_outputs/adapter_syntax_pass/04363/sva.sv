module top_module_sva (
    input logic clk,
    input logic reset,
    input logic enable,
    input logic [15:0] A,
    input logic [15:0] B,
    input logic [3:0] counter_out,
    input logic [15:0] adder_sum,
    input logic overflow,
    input logic [15:0] final_output
);

    // Counter is zero on the first cycle after reset is released.
    check_counter_zero_after_reset: assert property (
        @(posedge clk) disable iff (reset)
        $past(reset) |-> (counter_out == 4'h0)
    );

    // Counter increments by one when enable is high.
    check_counter_increments_when_enabled: assert property (
        @(posedge clk) disable iff (reset)
        enable |=> (counter_out == ($past(counter_out) + 4'h1))
    );

    // Counter holds its value when enable is low.
    check_counter_holds_when_disabled: assert property (
        @(posedge clk) disable iff (reset)
        !enable |=> (counter_out == $past(counter_out))
    );

    // Adder sum is the 16-bit sum of A and B.
    check_adder_sum_matches_inputs: assert property (
        @(posedge clk) disable iff (reset)
        adder_sum == (A + B)
    );

    // Overflow is asserted only when A and B have opposite sign bits.
    check_overflow_matches_inputs: assert property (
        @(posedge clk) disable iff (reset)
        overflow == ((A[15] & ~B[15]) | (~A[15] & B[15]))
    );

    // final_output is the 16-bit maximum of counter_out and adder_sum.
    check_final_output_matches_inputs: assert property (
        @(posedge clk) disable iff (reset)
        final_output == ((counter_out > adder_sum) ? counter_out : adder_sum)
    );

endmodule