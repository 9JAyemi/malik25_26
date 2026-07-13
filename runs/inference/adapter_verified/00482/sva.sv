module binary_multiplier_sva (
    input logic clk,
    input logic [3:0] a,
    input logic [3:0] b,
    input logic [7:0] out
);

// Output matches the RTL sum-of-products equation.
    check_full_sum_equation: assert property (
        @(posedge clk) out == (temp_out[0] + temp_out[1]*2 + temp_out[2]*4 + temp_out[3]*8 + temp_out[4]*16 + temp_out[5]*32 + temp_out[6]*64 + temp_out[7]*128)
    );

// Bit 0 of the output is a[0] AND b.
    check_bit0_from_a0_and_b: assert property (
        @(posedge clk) out[0] == (a[0] & b)
    );

// Bit 1 of the output is a[1] AND b.
    check_bit1_from_a1_and_b: assert property (
        @(posedge clk) out[1] == (a[1] & b)
    );

// Bit 2 of the output is a[2] AND b.
    check_bit2_from_a2_and_b: assert property (
        @(posedge clk) out[2] == (a[2] & b)
    );

// Bit 3 of the output is a[3] AND b.
    check_bit3_from_a3_and_b: assert property (
        @(posedge clk) out[3] == (a[3] & b)
    );

// Bits 4 through 7 are all zero.
    check_upper_bits_zero: assert property (
        @(posedge clk) out[7:4] == 4'h0
    );

endmodule
