module ripple_adder_sva (
    input logic CLK,
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [7:0] sum,
    input logic carry_out
);

// sum[0] matches the full-adder equation for bit 0.
    check_sum_bit0_equation: assert property (
        @(posedge CLK) sum[0] == (a[0] ^ b[0] ^ 1'b0)
    );

// sum[1] matches the full-adder equation for bit 1.
    check_sum_bit1_equation: assert property (
        @(posedge CLK) sum[1] == (a[1] ^ b[1] ^ c[1])
    );

// sum[2] matches the full-adder equation for bit 2.
    check_sum_bit2_equation: assert property (
        @(posedge CLK) sum[2] == (a[2] ^ b[2] ^ c[2])
    );

// sum[3] matches the full-adder equation for bit 3.
    check_sum_bit3_equation: assert property (
        @(posedge CLK) sum[3] == (a[3] ^ b[3] ^ c[3])
    );

// sum[4] matches the full-adder equation for bit 4.
    check_sum_bit4_equation: assert property (
        @(posedge CLK) sum[4] == (a[4] ^ b[4] ^ c[4])
    );

// sum[5] matches the full-adder equation for bit 5.
    check_sum_bit5_equation: assert property (
        @(posedge CLK) sum[5] == (a[5] ^ b[5] ^ c[5])
    );

// sum[6] matches the full-adder equation for bit 6.
    check_sum_bit6_equation: assert property (
        @(posedge CLK) sum[6] == (a[6] ^ b[6] ^ c[6])
    );

// sum[7] matches the full-adder equation for bit 7.
    check_sum_bit7_equation: assert property (
        @(posedge CLK) sum[7] == (a[7] ^ b[7] ^ c[7])
    );

// carry_out matches the full-adder equation for the final carry.
    check_carry_out_equation: assert property (
        @(posedge CLK) carry_out == ((a[7] & b[7]) | (c[7] & (a[7] ^ b[7])))
    );

endmodule
