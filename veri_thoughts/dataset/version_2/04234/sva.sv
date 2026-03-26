module top_module_sva (
    input logic clk,
    input logic reset,
    input logic [3:0] input_1,
    input logic [3:0] input_2,
    input logic [3:0] final_output,
    input logic [3:0] adder1_out,
    input logic [3:0] adder2_out
);

    // Reset clears both registers and the derived output on the next clock.
    check_reset_clears_pipeline: assert property (
        @(posedge clk)
        reset |=> (adder1_out == 4'b0000) && (adder2_out == 4'b0000) && (final_output == 4'b0000)
    );

    // adder1_out captures the previous cycle sum of input_1 and input_2.
    check_adder1_update: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (adder1_out == ($past(input_1) + $past(input_2)))
    );

    // adder2_out uses the previous registered adder1_out plus previous input_2.
    check_adder2_update: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (adder2_out == ($past(adder1_out) + $past(input_2)))
    );

    // final_output is the combinational sum of the two registered adders.
    check_final_output_sum: assert property (
        @(posedge clk) disable iff (reset)
        final_output == (adder1_out + adder2_out)
    );

    // The next-cycle output matches both adders' updates from the previous cycle.
    check_final_output_pipeline_result: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (final_output == (($past(input_1) + $past(input_2)) +
                                   ($past(adder1_out) + $past(input_2))))
    );

endmodule