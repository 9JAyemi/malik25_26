module adder4_assertions (
    input logic clk,
    input logic [3:0] a,
    input logic [3:0] b,
    input logic cin,
    input logic [3:0] sum,
    input logic cout
);

    // Full 5-bit output matches the zero-extended addition.
    check_full_result: assert property (
        @(posedge clk) disable iff (1'b0)
        {cout, sum} == ({1'b0, a} + {1'b0, b} + cin)
    );

    // Carry-out is high exactly when the total exceeds 15.
    check_cout_threshold: assert property (
        @(posedge clk) disable iff (1'b0)
        cout == (({1'b0, a} + {1'b0, b} + cin) > 5'd15)
    );

    // Sum bit 0 matches the LSB addition XOR relation.
    check_sum_lsb: assert property (
        @(posedge clk) disable iff (1'b0)
        sum[0] == (a[0] ^ b[0] ^ cin)
    );

    // Without carry-out, sum equals the full addition result.
    check_no_carry_sum: assert property (
        @(posedge clk) disable iff (1'b0)
        !cout |-> ({1'b0, sum} == ({1'b0, a} + {1'b0, b} + cin))
    );

    // With carry-out, sum holds the addition result modulo 16.
    check_carry_wrap_sum: assert property (
        @(posedge clk) disable iff (1'b0)
        cout |-> (({1'b0, sum} + 5'd16) == ({1'b0, a} + {1'b0, b} + cin))
    );

endmodule