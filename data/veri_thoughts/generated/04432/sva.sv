module sbox8_sva (
    input logic [6:1] Bin,
    input logic [4:1] BSout
);

    // No RTL clock or reset; sample combinational behavior on Jasper's global clock.
    // DUT is combinational; row bits are Bin[6] and Bin[1], and column bits are Bin[5:2].

    function automatic logic [4:1] exp_bsout(input logic [6:1] bin_in);
        begin
            case ({bin_in[6], bin_in[1], bin_in[5:2]})
                6'b000000: exp_bsout = 4'd13;
                6'b000001: exp_bsout = 4'd2;
                6'b000010: exp_bsout = 4'd8;
                6'b000011: exp_bsout = 4'd4;
                6'b000100: exp_bsout = 4'd6;
                6'b000101: exp_bsout = 4'd15;
                6'b000110: exp_bsout = 4'd11;
                6'b000111: exp_bsout = 4'd1;
                6'b001000: exp_bsout = 4'd10;
                6'b001001: exp_bsout = 4'd9;
                6'b001010: exp_bsout = 4'd3;
                6'b001011: exp_bsout = 4'd14;
                6'b001100: exp_bsout = 4'd5;
                6'b001101: exp_bsout = 4'd0;
                6'b001110: exp_bsout = 4'd12;
                6'b001111: exp_bsout = 4'd7;
                6'b010000: exp_bsout = 4'd1;
                6'b010001: exp_bsout = 4'd15;
                6'b010010: exp_bsout = 4'd13;
                6'b010011: exp_bsout = 4'd8;
                6'b010100: exp_bsout = 4'd10;
                6'b010101: exp_bsout = 4'd3;
                6'b010110: exp_bsout = 4'd7;
                6'b010111: exp_bsout = 4'd4;
                6'b011000: exp_bsout = 4'd12;
                6'b011001: exp_bsout = 4'd5;
                6'b011010: exp_bsout = 4'd6;
                6'b011011: exp_bsout = 4'd11;
                6'b011100: exp_bsout = 4'd0;
                6'b011101: exp_bsout = 4'd14;
                6'b011110: exp_bsout = 4'd9;
                6'b011111: exp_bsout = 4'd2;
                6'b100000: exp_bsout = 4'd7;
                6'b100001: exp_bsout = 4'd11;
                6'b100010: exp_bsout = 4'd4;
                6'b100011: exp_bsout = 4'd1;
                6'b100100: exp_bsout = 4'd9;
                6'b100101: exp_bsout = 4'd12;
                6'b100110: exp_bsout = 4'd14;
                6'b100111: exp_bsout = 4'd2;
                6'b101000: exp_bsout = 4'd0;
                6'b101001: exp_bsout = 4'd6;
                6'b101010: exp_bsout = 4'd10;
                6'b101011: exp_bsout = 4'd13;
                6'b101100: exp_bsout = 4'd15;
                6'b101101: exp_bsout = 4'd3;
                6'b101110: exp_bsout = 4'd5;
                6'b101111: exp_bsout = 4'd8;
                6'b110000: exp_bsout = 4'd2;
                6'b110001: exp_bsout = 4'd1;
                6'b110010: exp_bsout = 4'd14;
                6'b110011: exp_bsout = 4'd7;
                6'b110100: exp_bsout = 4'd4;
                6'b110101: exp_bsout = 4'd10;
                6'b110110: exp_bsout = 4'd8;
                6'b110111: exp_bsout = 4'd13;
                6'b111000: exp_bsout = 4'd15;
                6'b111001: exp_bsout = 4'd12;
                6'b111010: exp_bsout = 4'd9;
                6'b111011: exp_bsout = 4'd0;
                6'b111100: exp_bsout = 4'd3;
                6'b111101: exp_bsout = 4'd5;
                6'b111110: exp_bsout = 4'd6;
                6'b111111: exp_bsout = 4'd11;
                default:   exp_bsout = 4'd0;
            endcase
        end
    endfunction

    // BSout must match the S-box lookup selected by the reordered input bits.
    check_sbox8_lookup: assert property (
        @($global_clock) BSout == exp_bsout(Bin)
    );

endmodule