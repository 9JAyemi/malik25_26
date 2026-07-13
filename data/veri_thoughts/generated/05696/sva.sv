module XOR_32bit_sva (
    input logic [31:0] out,
    input logic [31:0] A,
    input logic [31:0] B
);

    // No clock or reset exists in the RTL; sample this combinational logic on $global_clock.
    // The DUT implements a purely combinational 32-bit bitwise XOR.

    // The full output vector must equal the bitwise XOR of A and B.
    check_out_matches_vector_xor: assert property (
        @($global_clock) out == (A ^ B)
    );

    genvar i;
    generate
        for (i = 0; i < 32; i = i + 1) begin : gen_bit_checks
            // Each output bit must equal the XOR of the corresponding input bits.
            check_out_bit_matches_xor: assert property (
                @($global_clock) out[i] == (A[i] ^ B[i])
            );
        end
    endgenerate

endmodule