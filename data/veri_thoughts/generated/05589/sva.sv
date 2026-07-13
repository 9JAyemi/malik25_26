module gray_converter_sva #(
    parameter n = 4
) (
    input logic         clk,
    input logic [n-1:0] bin,
    input logic [n-1:0] gray
);

    // Gray output matches the binary-to-gray conversion formula.
    check_gray_vector_encoding: assert property (
        @(posedge clk) gray == (bin ^ (bin >> 1))
    );

    // The MSB of gray is a direct copy of the MSB of bin.
    check_gray_msb_passthrough: assert property (
        @(posedge clk) gray[n-1] == bin[n-1]
    );

    genvar i;
    generate
        for (i = 0; i < n-1; i = i + 1) begin : gen_gray_bit_checks
            // Each lower gray bit is the XOR of adjacent binary bits.
            check_gray_bit_xor: assert property (
                @(posedge clk) gray[i] == (bin[i] ^ bin[i+1])
            );
        end
    endgenerate

endmodule