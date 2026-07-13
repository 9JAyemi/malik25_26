module top_module_sva (
    input logic       clk,
    input logic       reset,
    input logic [7:0] in_1,
    input logic [7:0] in_2,
    input logic       select,
    input logic [7:0] sum_output,
    input logic [7:0] or_output
);

    // When select is low, sum_output is the truncated sum of in_1 and in_2.
    check_sum_select_low: assert property (
        @(posedge clk) disable iff (reset)
        (select == 1'b0) |-> (sum_output == (in_1 + in_2))
    );

    // When select is high, sum_output is the truncated sum of in_2 and in_2.
    check_sum_select_high: assert property (
        @(posedge clk) disable iff (reset)
        (select == 1'b1) |-> (sum_output == (in_2 + in_2))
    );

    // When select is low, or_output is the bitwise OR of in_1 and in_2.
    check_or_select_low: assert property (
        @(posedge clk) disable iff (reset)
        (select == 1'b0) |-> (or_output == (in_1 | in_2))
    );

    // When select is high, or_output matches in_2 because in_2 is ORed with itself.
    check_or_select_high: assert property (
        @(posedge clk) disable iff (reset)
        (select == 1'b1) |-> (or_output == in_2)
    );

    // With in_2 equal to zero, sum_output passes the selected input through.
    check_sum_zero_in2_identity: assert property (
        @(posedge clk) disable iff (reset)
        (in_2 == 8'h00) |-> (sum_output == (select ? 8'h00 : in_1))
    );

    // With in_2 equal to zero, or_output passes the selected input through.
    check_or_zero_in2_identity: assert property (
        @(posedge clk) disable iff (reset)
        (in_2 == 8'h00) |-> (or_output == (select ? 8'h00 : in_1))
    );

    // Doubling in_2 produces an even result, so the LSB of sum_output is zero.
    check_double_sum_lsb_zero: assert property (
        @(posedge clk) disable iff (reset)
        (select == 1'b1) |-> (sum_output[0] == 1'b0)
    );

endmodule