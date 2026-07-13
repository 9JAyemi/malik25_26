module bin_to_gray_sva #(
    parameter int n = 4
) (
    input logic [n-1:0] bin,
    input logic [n-1:0] gray
);

    genvar i;

    // No explicit clock or reset exists in the RTL; sample on $global_clock.
    // The RTL is purely combinational and implements binary-to-Gray conversion.

    generate
        if (n == 1) begin : gen_single_bit
            // For 1-bit width, Gray code matches the binary input.
            check_gray_single_bit: assert property (
                @($global_clock) gray == bin
            );
        end else begin : gen_multi_bit
            // Gray output matches the RTL concatenation expression.
            check_gray_full_mapping: assert property (
                @($global_clock) gray == {bin[n-1], (bin[n-1:1] ^ bin[n-2:0])}
            );

            // The Gray MSB matches the binary MSB.
            check_gray_msb: assert property (
                @($global_clock) gray[n-1] == bin[n-1]
            );

            for (i = 0; i < n-1; i = i + 1) begin : gen_lower_bits
                // Each lower Gray bit is the XOR of adjacent binary bits.
                check_gray_adjacent_xor: assert property (
                    @($global_clock) gray[i] == (bin[i+1] ^ bin[i])
                );
            end
        end
    endgenerate

endmodule