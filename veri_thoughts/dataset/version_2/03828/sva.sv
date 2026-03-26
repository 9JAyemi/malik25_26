module gray_to_binary_decoder_sva #(
    parameter integer width = 32
)(
    input logic [width-1:0] gin,
    input logic [width-1:0] bout
);

    // No RTL clock or reset; sample the combinational decoder on the formal global clock.
    // The DUT converts Gray-coded input gin into binary output bout.

    function automatic logic [width-1:0] gray_to_binary(input logic [width-1:0] g);
        integer j;
        begin
            gray_to_binary = '0;
            gray_to_binary[width-1] = g[width-1];
            for (j = width-2; j >= 0; j = j - 1)
                gray_to_binary[j] = g[j] ^ gray_to_binary[j+1];
        end
    endfunction

    // The MSB of the binary output matches the MSB of the Gray input.
    check_msb_passthrough: assert property (
        @($global_clock) bout[width-1] == gin[width-1]
    );

    genvar i;
    generate
        for (i = 0; i < width-1; i = i + 1) begin : gen_recursive_checks
            // Each lower binary bit is the Gray bit XOR the next higher binary bit.
            check_recursive_decode: assert property (
                @($global_clock) bout[i] == (gin[i] ^ bout[i+1])
            );
        end
    endgenerate

    // The full output vector matches the Gray-to-binary decode of the input.
    check_full_decode: assert property (
        @($global_clock) bout == gray_to_binary(gin)
    );

endmodule