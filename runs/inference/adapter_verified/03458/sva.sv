module top_module_sva (
    input logic clk,
    input logic a1,
    input logic b1,
    input logic a2,
    input logic b2,
    input logic select,
    input logic [1:0] sum
);

// sum[1] is always 0 because the RTL adds two 1-bit numbers.
    check_sum_msb_zero: assert property (
        @(posedge clk) sum[1] == 1'b0
    );

// When select is 0, sum[0] equals the carry-out of the first half adder.
    check_select0_sum_lsb: assert property (
        @(posedge clk) !select |-> (sum[0] == ((a1 & b1) | ((a1 ^ b1) & 1'b0)))
    );

// When select is 1, sum[0] equals the carry-out of the second half adder.
    check_select1_sum_lsb: assert property (
        @(posedge clk) select |-> (sum[0] == ((a2 & b2) | ((a2 ^ b2) & 1'b0)))
    );

// sum[0] equals the carry-out of the selected half adder.
    check_sum_lsb_selected_adder: assert property (
        @(posedge clk) sum[0] == ((select ? (a2 & b2) : (a1 & b1)) | ((select ? (a2 ^ b2) : (a1 ^ b1)) & 1'b0))
    );

// sum equals the concatenation of the selected carry-out and the first half adder sum bit.
    check_sum_concatenation: assert property (
        @(posedge clk) sum == {((select ? (a2 & b2) : (a1 & b1)) | ((select ? (a2 ^ b2) : (a1 ^ b1)) & 1'b0)), ((a1 & b1) | ((a1 ^ b1) & 1'b0))}
    );

endmodule
