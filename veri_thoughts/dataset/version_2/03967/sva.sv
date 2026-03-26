module bin_to_gray_sva (
    input logic [31:0] bin_in,
    input logic [31:0] gray_out
);

    // No DUT clock or reset is present; sample on the global formal clock.

    // The output must match the bin-to-Gray conversion formula.
    check_gray_matches_formula: assert property (
        @($global_clock) disable iff (1'b0)
        gray_out == (bin_in ^ (bin_in >> 1))
    );

    // The Gray-code MSB must equal the binary MSB.
    check_msb_passthrough: assert property (
        @($global_clock) disable iff (1'b0)
        gray_out[31] == bin_in[31]
    );

    genvar i;
    generate
        for (i = 0; i < 31; i++) begin : gen_lower_bit_checks
            // Each lower Gray bit is the XOR of adjacent binary bits.
            check_adjacent_bit_xor: assert property (
                @($global_clock) disable iff (1'b0)
                gray_out[i] == (bin_in[i+1] ^ bin_in[i])
            );
        end
    endgenerate

endmodule