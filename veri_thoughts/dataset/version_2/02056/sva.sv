module bin_to_gray_sva (
    input  logic        CLK,
    input  logic [7:0]  bin_in,
    input  logic [7:0]  gray_out
);
    // Gray vector equals bin_in XOR (bin_in >> 1).
    check_gray_vector_equivalence: assert property (
        @(posedge CLK) gray_out == (bin_in ^ (bin_in >> 1))
    );

    // MSB of Gray equals MSB of binary input.
    check_gray_msb_mapping: assert property (
        @(posedge CLK) gray_out[7] == bin_in[7]
    );

    // Each Gray bit i (0..6) equals bin_in[i] XOR bin_in[i+1].
    genvar i;
    generate
        for (i = 0; i < 7; i++) begin : gen_gray_bit_checks
            check_gray_bit_mapping: assert property (
                @(posedge CLK) gray_out[i] == (bin_in[i] ^ bin_in[i+1])
            );
        end
    endgenerate
endmodule