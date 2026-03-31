module top_module_sva (
    input logic [31:0] a,
    input logic [31:0] b,
    input logic sub,
    input logic clk,
    input logic [31:0] result
);

// Result matches the RTL's conditional sum selection.
    check_result_mux_function: assert property (
        @(posedge clk) result == (sub ? sum2 : sum1)
    );

// When sub is low, result uses the low-16-bit adder sum.
    check_result_low16_when_sub_low: assert property (
        @(posedge clk) !sub |-> (result == {16'h0, sum1})
    );

// When sub is high, result uses the full 32-bit adder sum.
    check_result_full32_when_sub_high: assert property (
        @(posedge clk) sub |-> (result == sum2)
    );

// With sub low, the upper 16 bits of result are zero.
    check_result_upper_zero_when_sub_low: assert property (
        @(posedge clk) !sub |-> (result[31:16] == 16'h0)
    );

// With sub high, the upper 16 bits of result match the low-16-bit adder sum.
    check_result_upper_matches_low16_when_sub_high: assert property (
        @(posedge clk) sub |-> (result[31:16] == sum1)
    );

endmodule
