module four_bit_adder_sva (
    input logic clk,
    input logic [3:0] a,
    input logic [3:0] b,
    input logic cin,
    input logic [3:0] sum,
    input logic cout
);
    // Local expression helpers for ripple-carry chain
    let c1 = (a[0] & b[0]) | (a[0] & cin) | (b[0] & cin);
    let c2 = (a[1] & b[1]) | (a[1] & c1 ) | (b[1] & c1 );
    let c3 = (a[2] & b[2]) | (a[2] & c2 ) | (b[2] & c2 );
    let c4 = (a[3] & b[3]) | (a[3] & c3 ) | (b[3] & c3 );

    ///// Functional correctness /////
    // 5-bit result equals a + b + cin (unsigned addition).
    check_addition_result: assert property (
        @(posedge clk) {cout, sum} == ({1'b0, a} + {1'b0, b} + cin)
    );

    ///// Bit-slice correctness /////
    // LSB sum is XOR of a[0], b[0], and cin.
    check_sum0_xor: assert property (
        @(posedge clk) sum[0] == (a[0] ^ b[0] ^ cin)
    );
    // Bit1 sum is XOR of a[1], b[1], and carry from bit0.
    check_sum1_xor_with_c1: assert property (
        @(posedge clk) sum[1] == (a[1] ^ b[1] ^ c1)
    );
    // Bit2 sum is XOR of a[2], b[2], and carry from bit1.
    check_sum2_xor_with_c2: assert property (
        @(posedge clk) sum[2] == (a[2] ^ b[2] ^ c2)
    );
    // Bit3 sum is XOR of a[3], b[3], and carry from bit2.
    check_sum3_xor_with_c3: assert property (
        @(posedge clk) sum[3] == (a[3] ^ b[3] ^ c3)
    );
    // Carry-out equals carry generated at bit3.
    check_cout_matches_c4: assert property (
        @(posedge clk) cout == c4
    );

    ///// Simple corner cases /////
    // Adding zero and zero yields sum = cin on bit0 and cout = 0.
    check_zero_plus_zero: assert property (
        @(posedge clk) ((a == 4'b0000) && (b == 4'b0000)) |-> ((sum == {3'b000, cin}) && (cout == 1'b0))
    );
    // Adding zero with cin=0 passes through the other operand (a path).
    check_add_zero_b: assert property (
        @(posedge clk) ((b == 4'b0000) && (cin == 1'b0)) |-> ((sum == a) && (cout == 1'b0))
    );
    // Adding zero with cin=0 passes through the other operand (b path).
    check_add_zero_a: assert property (
        @(posedge clk) ((a == 4'b0000) && (cin == 1'b0)) |-> ((sum == b) && (cout == 1'b0))
    );
endmodule