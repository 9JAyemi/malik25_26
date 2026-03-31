```systemverilog
module adder_4bit_carry_sva (
    input logic [3:0] a,
    input logic [3:0] b,
    input logic cin,
    output logic [3:0] sum,
    output logic cout
);
    // Sequential logic is not present in this combinational module, so no need for clocked assertions.
    // The logic is purely combinational, so we will still use clocked assertions for consistency with the reference example.

    // Check that the sum is calculated correctly.
    sum_correct: assert property (
        @(posedge clk) disable iff (!resetn) (sum == (a + b + cin)[3:0])
    );

    // Check that the carry out is calculated correctly.
    carry_out_correct: assert property (
        @(posedge clk) disable iff (!resetn) (cout == (a + b + cin)[4])
    );

    // Check that the sum and carry out are not both high.
    no_overflow: assert property (
        @(posedge clk) disable iff (!resetn) !(sum == 4'b1111 && cout == 1'b1)
    );

    // Check that the sum and carry out are not both low.
    no_underflow: assert property (
        @(posedge clk) disable iff (!resetn) !(sum == 4'b0000 && cout == 1'b0)
    );

    // Check that the sum and carry out are within valid ranges.
    valid_range: assert property (
        @(posedge clk) disable iff (!resetn) (sum >= 4'b0000 && sum <= 4'b1111 && cout == 1'b0 || sum == 4'b0000 && cout == 1'b1)
    );

    // Check that the sum and carry out are not both zero when inputs are zero.
    non_zero_sum: assert property (
        @(posedge clk) disable iff (!resetn) !(a == 4'b0000 && b == 4'b0000 && cin == 1'b0 && sum == 4'b0000 && cout == 1'b0)
    );

    // Check that the sum and carry out are not both one when inputs are one.
    non_one_sum: assert property (
        @(posedge clk) disable iff (!resetn) !(a == 4'b1111 && b == 4'b1111 && cin == 1'b1 && sum == 4'b1111 && cout == 1'b1)
    );

    // Check that the sum and carry out are not both zero when inputs are one and carry in is zero.
    non_zero_sum_cin_zero: assert property (
        @(posedge clk) disable iff (!resetn) !(a == 4'b1111 && b == 4'b1111 && cin == 1'b0 && sum == 4'b0000 && cout == 1'b0)
    );

    // Check that the sum and carry out are not both one when inputs are zero and carry in is one.
    non_one_sum_cin_one: assert property (
        @(posedge clk) disable iff (!resetn) !(a == 4'b0000 && b == 4'b0000 && cin == 1'b1 && sum == 4'b1111 && cout == 1'b1)
    );

    // Check that the sum and carry out are not both zero when inputs are one and carry in is one.
    non_zero_sum_cin_one: assert property (
        @(posedge clk) disable iff (!resetn) !(a == 4'b1111 && b == 4'b1111 && cin == 1'b1 && sum == 4'b0000 && cout == 1'b0)
    );

    // Check that the sum and carry out are not both one when inputs are zero and carry in is zero.
    non_one_sum_cin_zero: assert property (
        @(posedge clk) disable iff (!resetn) !(a == 4'b0000 && b == 4'b0000 && cin == 1'b0 && sum == 4'b1111 && cout == 1'b1)
    );
endmodule
```