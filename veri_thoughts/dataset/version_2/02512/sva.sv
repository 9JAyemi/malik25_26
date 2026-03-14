module top_module_sva (
    input logic clk,          // Sampling clock for assertions (RTL has no clock/reset)
    input logic [3:0] a,
    input logic [3:0] b,
    input logic [4:0] sum
);
    // Local carry chain derived from inputs for checking only
    logic c0, c1, c2;
    assign c0 = a[0] & b[0];
    assign c1 = (a[1] & b[1]) | (a[1] & c0) | (b[1] & c0);
    assign c2 = (a[2] & b[2]) | (a[2] & c1) | (b[2] & c1);

    ///// Functional correctness /////
    // 5-bit sum equals zero-extended a + b.
    check_sum_matches_add: assert property (
        @(posedge clk) sum == ({1'b0, a} + {1'b0, b})
    );

    // LSB sum is XOR of a[0] and b[0] (cin=0).
    check_sum0_xor: assert property (
        @(posedge clk) sum[0] == (a[0] ^ b[0])
    );

    // Bit1 sum uses carry from bit0.
    check_sum1_ripple: assert property (
        @(posedge clk) sum[1] == (a[1] ^ b[1] ^ c0)
    );

    // Bit2 sum uses carry from bit1.
    check_sum2_ripple: assert property (
        @(posedge clk) sum[2] == (a[2] ^ b[2] ^ c1)
    );

    // Bit3 sum uses carry from bit2.
    check_sum3_ripple: assert property (
        @(posedge clk) sum[3] == (a[3] ^ b[3] ^ c2)
    );

    // MSB carry-out equals majority of a[3], b[3], and c2.
    check_sum4_carryout: assert property (
        @(posedge clk) sum[4] == ((a[3] & b[3]) | (a[3] & c2) | (b[3] & c2))
    );

    // Lower 4 bits of sum match arithmetic sum low nibble.
    check_low_nibble_match: assert property (
        @(posedge clk) sum[3:0] == ({1'b0, a} + {1'b0, b})[3:0]
    );

    // Adding zero on a yields sum == b.
    check_add_zero_a: assert property (
        @(posedge clk) (a == 4'b0000) |-> (sum == {1'b0, b})
    );

    // Adding zero on b yields sum == a.
    check_add_zero_b: assert property (
        @(posedge clk) (b == 4'b0000) |-> (sum == {1'b0, a})
    );
endmodule