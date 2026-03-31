module top_module_sva (
    input logic        clk,
    input logic [31:0] a,
    input logic [31:0] b,
    input logic        select,
    input logic [31:0] sum
);

// Sum must match the RTL's conditional path.
    check_sum_function: assert property (
        @(posedge clk) sum == ((select == 1'b1) ? a + b : {31'b0, a[0]})
    );

// When select is high, sum must be the 32-bit addition of a and b.
    check_sum_when_select_high: assert property (
        @(posedge clk) (select == 1'b1) |-> (sum == (a + b))
    );

// When select is low, sum must be zero-extended a[0].
    check_sum_when_select_low: assert property (
        @(posedge clk) (select == 1'b0) |-> (sum == {31'b0, a[0]})
    );

// A high select must force the lower 31 bits of sum to zero.
    check_sum_lower_bits_zero_when_select_high: assert property (
        @(posedge clk) (select == 1'b1) |-> (sum[30:0] == 31'b0)
    );

// A low select must force the upper 31 bits of sum to zero.
    check_sum_upper_bits_zero_when_select_low: assert property (
        @(posedge clk) (select == 1'b0) |-> (sum[31:1] == 31'b0)
    );

// A high select must pass a[0] through to the least-significant bit.
    check_sum_lsb_when_select_high: assert property (
        @(posedge clk) (select == 1'b1) |-> (sum[0] == a[0])
    );

// A low select must pass a[0] through to the least-significant bit.
    check_sum_lsb_when_select_low: assert property (
        @(posedge clk) (select == 1'b0) |-> (sum[0] == a[0])
    );

endmodule
