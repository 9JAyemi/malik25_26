module adder4bit_sva (
    input logic CLK,
    input logic [3:0] a,
    input logic [3:0] b,
    input logic cin,
    input logic [3:0] sum,
    input logic cout
);
    // Local derived ripple carries from inputs
    logic c0, c1, c2;
    assign c0 = (a[0] & b[0]) | (a[0] & cin) | (b[0] & cin);
    assign c1 = (a[1] & b[1]) | (a[1] & c0) | (b[1] & c0);
    assign c2 = (a[2] & b[2]) | (a[2] & c1) | (b[2] & c1);

    ///// Functional correctness /////
    // 5-bit result equals a + b + cin.
    check_add_result: assert property (
        @(posedge CLK) disable iff (1'b0) {cout, sum} == ({1'b0, a} + {1'b0, b} + cin)
    );
    // sum[0] is XOR of a[0], b[0], cin.
    check_sum0_xor: assert property (
        @(posedge CLK) disable iff (1'b0) sum[0] == (a[0] ^ b[0] ^ cin)
    );
    // sum[1] is XOR of a[1], b[1], and carry from bit 0.
    check_sum1_xor: assert property (
        @(posedge CLK) disable iff (1'b0) sum[1] == (a[1] ^ b[1] ^ c0)
    );
    // sum[2] is XOR of a[2], b[2], and carry from bit 1.
    check_sum2_xor: assert property (
        @(posedge CLK) disable iff (1'b0) sum[2] == (a[2] ^ b[2] ^ c1)
    );
    // sum[3] is XOR of a[3], b[3], and carry from bit 2.
    check_sum3_xor: assert property (
        @(posedge CLK) disable iff (1'b0) sum[3] == (a[3] ^ b[3] ^ c2)
    );
    // cout is majority of a[3], b[3], and carry from bit 2.
    check_cout_majority: assert property (
        @(posedge CLK) disable iff (1'b0) cout == ((a[3] & b[3]) | (a[3] & c2) | (b[3] & c2))
    );
endmodule