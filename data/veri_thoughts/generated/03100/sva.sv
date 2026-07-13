module top_module_sva (
    input logic [31:0] a,
    input logic [31:0] b,
    input logic sub,
    input logic clk,
    input logic [31:0] result
);

    // In add mode, the low 16 bits are the sum of a[15:0] and b[15:0].
    check_add_mode_lower_sum: assert property (
        @(posedge clk) (sub == 1'b0) |-> (result[15:0] == (a[15:0] + b[15:0]))
    );

    // In add mode, the selected 16-bit sum is zero-extended to 32 bits.
    check_add_mode_upper_zero: assert property (
        @(posedge clk) (sub == 1'b0) |-> (result[31:16] == 16'h0000)
    );

    // In sub-selected mode, the low 16 bits are sum1 + b[15:0] + 1.
    check_sub_mode_lower_sum: assert property (
        @(posedge clk) (sub == 1'b1) |-> (result[15:0] == (a[15:0] + b[15:0] + b[15:0] + 16'h0001))
    );

    // In sub-selected mode, no carry from the low add leaves the upper sum unchanged.
    check_sub_mode_upper_no_carry: assert property (
        @(posedge clk)
        ((sub == 1'b1) && (({1'b0, a[15:0]} + {1'b0, b[15:0]}) < 17'h10000))
        |-> (result[31:16] == (a[31:16] + b[31:16]))
    );

    // In sub-selected mode, a carry from the low add increments the upper sum.
    check_sub_mode_upper_with_carry: assert property (
        @(posedge clk)
        ((sub == 1'b1) && (({1'b0, a[15:0]} + {1'b0, b[15:0]}) >= 17'h10000))
        |-> (result[31:16] == (a[31:16] + b[31:16] + 16'h0001))
    );

endmodule