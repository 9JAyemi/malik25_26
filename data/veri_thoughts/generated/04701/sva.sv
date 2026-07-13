module dectohexstr8_sva (
    input logic        clk,
    input logic [7:0]  in,
    input logic [15:0] out
);

    function automatic [7:0] hex_ascii(input logic [3:0] nibble);
        begin
            hex_ascii = (nibble == 4'd0)  ? "0" :
                        (nibble == 4'd1)  ? "1" :
                        (nibble == 4'd2)  ? "2" :
                        (nibble == 4'd3)  ? "3" :
                        (nibble == 4'd4)  ? "4" :
                        (nibble == 4'd5)  ? "5" :
                        (nibble == 4'd6)  ? "6" :
                        (nibble == 4'd7)  ? "7" :
                        (nibble == 4'd8)  ? "8" :
                        (nibble == 4'd9)  ? "9" :
                        (nibble == 4'd10) ? "A" :
                        (nibble == 4'd11) ? "B" :
                        (nibble == 4'd12) ? "C" :
                        (nibble == 4'd13) ? "D" :
                        (nibble == 4'd14) ? "E" : "F";
        end
    endfunction

    // Low nibble is converted to its ASCII hex character.
    check_low_nibble_ascii_encoding: assert property (
        @(posedge clk) out[7:0] == hex_ascii(in[3:0])
    );

    // High nibble is converted to its ASCII hex character.
    check_high_nibble_ascii_encoding: assert property (
        @(posedge clk) out[15:8] == hex_ascii(in[7:4])
    );

    // Full output is the concatenation of high and low ASCII hex characters.
    check_full_output_encoding: assert property (
        @(posedge clk) out == {hex_ascii(in[7:4]), hex_ascii(in[3:0])}
    );

    // Input 8'h00 maps to ASCII "00".
    check_zero_input_maps_to_ascii_00: assert property (
        @(posedge clk) (in == 8'h00) |-> (out == {"0", "0"})
    );

    // Input 8'hFF maps to ASCII "FF".
    check_ff_input_maps_to_ascii_ff: assert property (
        @(posedge clk) (in == 8'hFF) |-> (out == {"F", "F"})
    );

endmodule