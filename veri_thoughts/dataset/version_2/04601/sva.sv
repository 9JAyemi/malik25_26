module top_module_sva (
    input logic        clk,
    input logic [15:0] a,
    input logic [15:0] b,
    input logic        select,
    input logic [31:0] sum
);

    // Upper 16 bits are always zero for both output paths.
    check_sum_upper_zero: assert property (
        @(posedge clk) disable iff (1'b0)
        sum[31:16] == 16'h0000
    );

    // When select is low, sum is the zero-extended 16-bit result of a + b.
    check_sum_select_low: assert property (
        @(posedge clk) disable iff (1'b0)
        !select |-> (sum == {16'h0000, (a + b)})
    );

    // When select is high, sum is the zero-extended 16-bit result of (a + b) + (a + b).
    check_sum_select_high: assert property (
        @(posedge clk) disable iff (1'b0)
        select |-> (sum == {16'h0000, ((a + b) + (a + b))})
    );

    // The low 16 bits follow the selected datapath function.
    check_sum_low_half_function: assert property (
        @(posedge clk) disable iff (1'b0)
        sum[15:0] == (select ? ((a + b) + (a + b)) : (a + b))
    );

endmodule