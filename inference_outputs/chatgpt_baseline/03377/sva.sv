module hex_display_sva #(
    parameter INVERT = 0
) (
    input logic       clk,
    input logic [3:0] in,
    input logic       enable,
    input logic [6:0] out
);

    function automatic logic [6:0] hex_enc(input logic [3:0] value);
        begin
            hex_enc = 7'b0000000;
            case (value)
                4'h0: hex_enc = 7'b0111111;
                4'h1: hex_enc = 7'b0000110;
                4'h2: hex_enc = 7'b1011011;
                4'h3: hex_enc = 7'b1001111;
                4'h4: hex_enc = 7'b1100110;
                4'h5: hex_enc = 7'b1101101;
                4'h6: hex_enc = 7'b1111101;
                4'h7: hex_enc = 7'b0000111;
                4'h8: hex_enc = 7'b1111111;
                4'h9: hex_enc = 7'b1101111;
                4'ha: hex_enc = 7'b1110111;
                4'hb: hex_enc = 7'b1111100;
                4'hc: hex_enc = 7'b0111001;
                4'hd: hex_enc = 7'b1011110;
                4'he: hex_enc = 7'b1111001;
                4'hf: hex_enc = 7'b1110001;
            endcase
        end
    endfunction

    // Disabled display outputs a blank pattern.
    check_blank_when_disabled: assert property (
        @(posedge clk) !enable |-> out == (INVERT ? ~7'b0000000 : 7'b0000000)
    );

    // Enabled display outputs the selected hex digit pattern.
    check_enabled_hex_decode: assert property (
        @(posedge clk) enable |-> out == (INVERT ? ~hex_enc(in) : hex_enc(in))
    );

endmodule