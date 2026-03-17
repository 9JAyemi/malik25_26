module ripple_carry_adder_assertions (
    input logic clk,
    input logic [3:0] a,
    input logic [3:0] b,
    input logic [3:0] sum,
    input logic carry_out
);

    // Full 5-bit result matches unsigned addition.
    check_full_addition: assert property (
        @(posedge clk) {carry_out, sum} == ({1'b0, a} + {1'b0, b})
    );

    // Bit 0 has no carry-in, so it is the XOR of the input bits.
    check_lsb_sum: assert property (
        @(posedge clk) sum[0] == (a[0] ^ b[0])
    );

    // The low two sum bits match 2-bit addition.
    check_low_two_bits: assert property (
        @(posedge clk) sum[1:0] == (a[1:0] + b[1:0])
    );

    // The low three sum bits match 3-bit addition.
    check_low_three_bits: assert property (
        @(posedge clk) sum[2:0] == (a[2:0] + b[2:0])
    );

    // The carry output matches the overflow bit of the extended sum.
    check_carry_out: assert property (
        @(posedge clk) carry_out == ({1'b0, a} + {1'b0, b})[4]
    );

    // Adding zero on a leaves b unchanged and produces no carry.
    check_a_zero_identity: assert property (
        @(posedge clk) (a == 4'h0) |-> (sum == b && carry_out == 1'b0)
    );

    // Adding zero on b leaves a unchanged and produces no carry.
    check_b_zero_identity: assert property (
        @(posedge clk) (b == 4'h0) |-> (sum == a && carry_out == 1'b0)
    );

    // Adding 4'hF and 4'hF produces 4'hE with carry-out set.
    check_max_plus_max: assert property (
        @(posedge clk) ((a == 4'hF) && (b == 4'hF)) |-> (sum == 4'hE && carry_out == 1'b1)
    );

endmodule