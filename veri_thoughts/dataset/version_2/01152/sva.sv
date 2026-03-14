module binary_adder_sva (
    input logic clk,
    input logic [3:0] a,
    input logic [3:0] b,
    input logic [3:0] sum
);
    // Combinational module with no reset; use clk only for sampling assertions.

    // Sum must equal the low 4 bits of a + b (modulo-16 addition).
    check_sum_mod16: assert property (
        @(posedge clk) sum == (a + b)[3:0]
    );

    // Adding zero on b leaves sum equal to a.
    check_add_zero_b: assert property (
        @(posedge clk) (b == 4'd0) |-> (sum == a)
    );

    // Adding zero on a leaves sum equal to b.
    check_add_zero_a: assert property (
        @(posedge clk) (a == 4'd0) |-> (sum == b)
    );

    // Specific wrap case: 8 + 8 = 16 -> sum wraps to 0.
    check_wrap_8_8: assert property (
        @(posedge clk) (a == 4'd8 && b == 4'd8) |-> (sum == 4'd0)
    );

    // Specific wrap case: 15 + 1 = 16 -> sum wraps to 0.
    check_wrap_15_1: assert property (
        @(posedge clk) (a == 4'd15 && b == 4'd1) |-> (sum == 4'd0)
    );

    // Specific case: 15 + 15 = 30 -> sum is 14 (0xE).
    check_case_15_15: assert property (
        @(posedge clk) (a == 4'd15 && b == 4'd15) |-> (sum == 4'd14)
    );

    // If inputs are stable, the output must be stable (pure combinational function).
    check_stability_when_inputs_stable: assert property (
        @(posedge clk) ($stable(a) && $stable(b)) |-> $stable(sum)
    );

    // LSB property of addition: sum[0] equals a[0] XOR b[0].
    check_lsb_xor: assert property (
        @(posedge clk) sum[0] == (a[0] ^ b[0])
    );

    // On overflow (a+b >= 16), sum equals (a+b-16) i.e., the low 4 bits.
    check_overflow_wrap_general: assert property (
        @(posedge clk) ((({1'b0, a} + {1'b0, b}) >= 5'd16)) |-> (sum == (({1'b0, a} + {1'b0, b}) - 5'd16)[3:0])
    );

    // On no overflow (a+b < 16), sum equals the full addition result.
    check_no_overflow_exact: assert property (
        @(posedge clk) ((({1'b0, a} + {1'b0, b}) < 5'd16)) |-> (sum == (a + b)[3:0])
    );

endmodule