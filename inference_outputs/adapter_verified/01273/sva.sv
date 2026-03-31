module top_module_sva (
    input logic        clk,
    input logic [31:0] a,
    input logic [31:0] b,
    input logic [31:0] sum
);

// The low 16 bits of sum equal the low 16 bits of a plus b.
    check_low_sum_matches_addition: assert property (
        @(posedge clk) sum[15:0] == (a[15:0] + b[15:0])
    );

// The high 16 bits of sum equal the high 16 bits of a plus b plus the low-sum carry.
    check_high_sum_matches_addition: assert property (
        @(posedge clk) sum[31:16] == (a[31:16] + b[31:16] + ((a[15:0] + b[15:0]) >= 16'h10000))
    );

// Zero plus zero yields zero.
    check_zero_plus_zero: assert property (
        @(posedge clk) (a == 32'h0) && (b == 32'h0) |-> (sum == 32'h0)
    );

// Zero on b passes a through unchanged.
    check_zero_b_passthrough: assert property (
        @(posedge clk) (b == 32'h0) |-> (sum == a)
    );

// Zero on a passes b through unchanged.
    check_zero_a_passthrough: assert property (
        @(posedge clk) (a == 32'h0) |-> (sum == b)
    );

// Adding one to zero yields one.
    check_one_plus_zero: assert property (
        @(posedge clk) (a == 32'h0) && (b == 32'h1) |-> (sum == 32'h1)
    );

// Adding zero to one yields one.
    check_zero_plus_one: assert property (
        @(posedge clk) (b == 32'h0) && (a == 32'h1) |-> (sum == 32'h1)
    );

// The maximum 16-bit value plus one wraps to zero with carry out.
    check_max_plus_one: assert property (
        @(posedge clk) (a == 32'hFFFF) && (b == 32'h0001) |-> (sum == 32'h0000)
    );

// The maximum 16-bit value plus itself wraps to zero with carry out.
    check_max_plus_max: assert property (
        @(posedge clk) (a == 32'hFFFF) && (b == 32'hFFFF) |-> (sum == 32'h0000)
    );

endmodule
