module top_module_sva (
    input logic clk,
    input logic reset,
    input logic enable,
    input logic [15:0] A,
    input logic [15:0] B,
    output logic [3:0] counter_out,
    output logic [15:0] adder_sum,
    output logic overflow,
    output logic [15:0] final_output
);

    // Counter module properties
    // Counter increments on rising edge of clk when enable is high and reset is low
    counter_increment: assert property (
        @(posedge clk) disable iff (!reset) (enable && counter_out != 4'b1111) |-> counter_out == counter_out + 1
    );
    // Counter resets to 0 on rising edge of clk when reset is high
    counter_reset: assert property (
        @(posedge clk) disable iff (!reset) reset |-> counter_out == 4'b0
    );

    // Ripple carry adder properties
    // Adder sum is correct for given A and B
    adder_correct: assert property (
        @(posedge clk) disable iff (!reset) adder_sum == A + B
    );
    // Overflow is set correctly based on A and B
    overflow_correct: assert property (
        @(posedge clk) disable iff (!reset) overflow == ((A[15] & B[15] & ~adder_sum[15]) | (~A[15] & ~B[15] & adder_sum[15]))
    );

    // Final output properties
    // Final output is the maximum of counter_out and adder_sum
    final_output_correct: assert property (
        @(posedge clk) disable iff (!reset) final_output == (counter_out > adder_sum) ? counter_out : adder_sum
    );

endmodule