module ripple_adder_64_sva (
    input logic        clk,
    input logic [63:0] A,
    input logic [63:0] B,
    input logic [63:0] SUM,
    input logic        CARRY
);

    // The full output must equal the 65-bit sum of A and B.
    check_full_addition: assert property (
        @(posedge clk) {CARRY, SUM} == ({1'b0, A} + {1'b0, B})
    );

    // Bit 0 is the xor of the input LSBs.
    check_sum_bit0: assert property (
        @(posedge clk) SUM[0] == (A[0] ^ B[0])
    );

    genvar i;
    generate
        for (i = 1; i < 64; i = i + 1) begin : gen_sum_bit_checks
            // Each higher sum bit includes the carry from the lower slice addition.
            check_sum_bit: assert property (
                @(posedge clk)
                SUM[i] == (A[i] ^ B[i] ^ (({1'b0, A[i-1:0]} + {1'b0, B[i-1:0]})[i]))
            );
        end
    endgenerate

    // The final carry matches the overflow of the 64-bit addition.
    check_final_carry: assert property (
        @(posedge clk) CARRY == ({1'b0, A} + {1'b0, B})[64]
    );

    // The MSB carry-out follows the full-adder carry equation.
    check_msb_carry_equation: assert property (
        @(posedge clk)
        CARRY == (
            (A[63] & B[63]) |
            (A[63] & ({1'b0, A[62:0]} + {1'b0, B[62:0]})[63]) |
            (B[63] & ({1'b0, A[62:0]} + {1'b0, B[62:0]})[63])
        )
    );

endmodule