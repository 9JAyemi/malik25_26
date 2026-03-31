```systemverilog
module top_module_sva (
    input logic a1, b1, a2, b2, // 4 input bits for the two binary numbers
    input logic select, // Select input to choose between carry-out of first half adder and second half adder
    output logic [1:0] sum // 2-bit output for the sum of the two binary numbers
);

    wire carry1, carry2;
    wire sum1, sum2;

    binary_adder adder1(a1, b1, 1'b0, sum1, carry1);
    binary_adder adder2(a2, b2, 1'b0, sum2, carry2);

    // The sum output is the result of adding the two sums and the selected carry-out
    sum_calculation: assert property (
        @(posedge clk) disable iff (!resetn) sum == ({select ? carry2 : carry1, sum1} + sum2)
    );

    // The carry-out of the first adder is the sum of the two input bits
    carry1_calculation: assert property (
        @(posedge clk) disable iff (!resetn) carry1 == (a1 & b1)
    );

    // The carry-out of the second adder is the sum of the two input bits
    carry2_calculation: assert property (
        @(posedge clk) disable iff (!resetn) carry2 == (a2 & b2)
    );

    // The sum of the two input bits is the XOR of the two input bits
    sum1_calculation: assert property (
        @(posedge clk) disable iff (!resetn) sum1 == (a1 ^ b1)
    );

    // The sum of the two input bits is the XOR of the two input bits
    sum2_calculation: assert property (
        @(posedge clk) disable iff (!resetn) sum2 == (a2 ^ b2)
    );

endmodule
```