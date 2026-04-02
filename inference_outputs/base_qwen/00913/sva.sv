module top_module_sva (
    input logic clk,
    input logic reset,
    input logic [3:0] a,
    input logic [3:0] b,
    input logic ctrl,
    output logic [3:0] out_adder,
    output logic [2:0] out_comparator
);
    // Adder output should be the sum of a and b
    adder_output_check: assert property (
        @(posedge clk) disable iff (!reset) (out_adder == a + b)
    );

    // Comparator output should be 3'b100 if a > b, 3'b010 if a == b, and 3'b001 if a < b
    comparator_output_check: assert property (
        @(posedge clk) disable iff (!reset) 
        (out_comparator == (a > b) ? 3'b100 : (a == b) ? 3'b010 : 3'b001)
    );

    // Mux output should be the same as adder output when ctrl is 0
    mux_output_check_0: assert property (
        @(posedge clk) disable iff (!reset) (ctrl == 1'b0) |-> (out_adder == out_comparator)
    );

    // Mux output should be the same as comparator output when ctrl is 1
    mux_output_check_1: assert property (
        @(posedge clk) disable iff (!reset) (ctrl == 1'b1) |-> (out_comparator == out_comparator)
    );

    // Adder output should be within the range of 0 to 15
    adder_output_range_check: assert property (
        @(posedge clk) disable iff (!reset) (out_adder inside {[0:15]})
    );

    // Comparator output should be within the range of 0 to 7
    comparator_output_range_check: assert property (
        @(posedge clk) disable iff (!reset) (out_comparator inside {[0:7]})
    );

    // Adder output should be the same as a + b
    adder_output_correctness_check: assert property (
        @(posedge clk) disable iff (!reset) (out_adder == a + b)
    );

    // Comparator output should be correct based on the comparison of a and b
    comparator_output_correctness_check: assert property (
        @(posedge clk) disable iff (!reset) 
        (out_comparator == (a > b) ? 3'b100 : (a == b) ? 3'b010 : 3'b001)
    );

    // Mux output should be the same as adder output when ctrl is 0
    mux_output_correctness_check_0: assert property (
        @(posedge clk) disable iff (!reset) (ctrl == 1'b0) |-> (out_adder == out_comparator)
    );

    // Mux output should be the same as comparator output when ctrl is 1
    mux_output_correctness_check_1: assert property (
        @(posedge clk) disable iff (!reset) (ctrl == 1'b1) |-> (out_comparator == out_comparator)
    );
endmodule