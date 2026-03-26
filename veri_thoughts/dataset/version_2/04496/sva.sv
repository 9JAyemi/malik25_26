module dectohexstr24_sva (
    input logic clk,
    input logic [23:0] in,
    input logic [127:0] out
);

    function automatic logic [7:0] hex_ascii(input logic [3:0] nib);
        hex_ascii = (nib == 4'd0)  ? "0" :
                    (nib == 4'd1)  ? "1" :
                    (nib == 4'd2)  ? "2" :
                    (nib == 4'd3)  ? "3" :
                    (nib == 4'd4)  ? "4" :
                    (nib == 4'd5)  ? "5" :
                    (nib == 4'd6)  ? "6" :
                    (nib == 4'd7)  ? "7" :
                    (nib == 4'd8)  ? "8" :
                    (nib == 4'd9)  ? "9" :
                    (nib == 4'd10) ? "A" :
                    (nib == 4'd11) ? "B" :
                    (nib == 4'd12) ? "C" :
                    (nib == 4'd13) ? "D" :
                    (nib == 4'd14) ? "E" : "F";
    endfunction

    // Upper ten bytes are constant space padding.
    check_upper_space_padding: assert property (
        @(posedge clk) out[127:48] === 80'h20202020202020202020
    );

    // Output [15:0] is the ASCII hex encoding of input byte [7:0].
    check_low_byte_ascii_hex: assert property (
        @(posedge clk) out[15:0] === {hex_ascii(in[7:4]), hex_ascii(in[3:0])}
    );

    // Output [31:16] is the ASCII hex encoding of input byte [15:8].
    check_middle_byte_ascii_hex: assert property (
        @(posedge clk) out[31:16] === {hex_ascii(in[15:12]), hex_ascii(in[11:8])}
    );

    // Output [47:32] is the ASCII hex encoding of input byte [23:16].
    check_high_byte_ascii_hex: assert property (
        @(posedge clk) out[47:32] === {hex_ascii(in[23:20]), hex_ascii(in[19:16])}
    );

endmodule