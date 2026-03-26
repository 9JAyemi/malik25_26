module GrayCodeConverter_sva #(
    parameter n = 4
) (
    input logic         clk,
    input logic [n-1:0] bin,
    input logic [n-1:0] gray
);

    // Gray output matches the implemented conversion equation.
    check_gray_equation: assert property (
        @(posedge clk) gray == (bin ^ (bin >> 1))
    );

    // The Gray MSB is the same as the binary MSB.
    check_gray_msb_passthrough: assert property (
        @(posedge clk) gray[n-1] == bin[n-1]
    );

    // A stable binary input yields a stable Gray output.
    check_gray_stable_when_bin_stable: assert property (
        @(posedge clk) $stable(bin) |-> $stable(gray)
    );

    genvar i;
    generate
        for (i = 0; i < n-1; i = i + 1) begin : gen_gray_lower_bit_checks
            // Each lower Gray bit is the XOR of adjacent binary bits.
            check_gray_adjacent_xor: assert property (
                @(posedge clk) gray[i] == (bin[i+1] ^ bin[i])
            );
        end
    endgenerate

endmodule