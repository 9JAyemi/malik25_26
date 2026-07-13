module four_bit_adder_sva (
    input logic       clk,
    input logic [3:0] a,
    input logic [3:0] b,
    input logic       c_in,
    input logic [3:0] s,
    input logic       c_out
);

    // No clock or reset exists in the RTL; clk is an external sampling clock.

    // Full 5-bit result must equal a + b + c_in.
    check_total_sum: assert property (
        @(posedge clk)
        {c_out, s} == ({1'b0, a} + {1'b0, b} + {4'b0000, c_in})
    );

    // Bit 0 sum must be the XOR of the three bit-0 inputs.
    check_bit0_sum: assert property (
        @(posedge clk)
        s[0] == (a[0] ^ b[0] ^ c_in)
    );

    // Bit 1 sum must match the bit-1 result of adding the low 2 bits plus c_in.
    check_bit1_sum: assert property (
        @(posedge clk)
        s[1] == (({1'b0, a[1:0]} + {1'b0, b[1:0]} + {2'b00, c_in})[1])
    );

    // Bit 2 sum must match the bit-2 result of adding the low 3 bits plus c_in.
    check_bit2_sum: assert property (
        @(posedge clk)
        s[2] == (({1'b0, a[2:0]} + {1'b0, b[2:0]} + {3'b000, c_in})[2])
    );

    // Bit 3 sum must match the bit-3 result of adding all 4 bits plus c_in.
    check_bit3_sum: assert property (
        @(posedge clk)
        s[3] == (({1'b0, a} + {1'b0, b} + {4'b0000, c_in})[3])
    );

    // Carry out must match the MSB of the 5-bit addition result.
    check_carry_out: assert property (
        @(posedge clk)
        c_out == (({1'b0, a} + {1'b0, b} + {4'b0000, c_in})[4])
    );

endmodule