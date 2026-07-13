module sbox7_sva (
    input logic clk,
    input logic [6:1] Bin,
    input logic [4:1] BSout
);

    function automatic logic [4:1] sbox7_model(input logic [6:1] bin_i);
        begin
            case ({bin_i[6], bin_i[1], bin_i[5:2]})
                6'b000000: sbox7_model = 4'd4;
                6'b000001: sbox7_model = 4'd11;
                6'b000010: sbox7_model = 4'd2;
                6'b000011: sbox7_model = 4'd14;
                6'b000100: sbox7_model = 4'd15;
                6'b000101: sbox7_model = 4'd0;
                6'b000110: sbox7_model = 4'd8;
                6'b000111: sbox7_model = 4'd13;
                6'b001000: sbox7_model = 4'd3;
                6'b001001: sbox7_model = 4'd12;
                6'b001010: sbox7_model = 4'd9;
                6'b001011: sbox7_model = 4'd7;
                6'b001100: sbox7_model = 4'd5;
                6'b001101: sbox7_model = 4'd10;
                6'b001110: sbox7_model = 4'd6;
                6'b001111: sbox7_model = 4'd1;
                6'b010000: sbox7_model = 4'd13;
                6'b010001: sbox7_model = 4'd0;
                6'b010010: sbox7_model = 4'd11;
                6'b010011: sbox7_model = 4'd7;
                6'b010100: sbox7_model = 4'd4;
                6'b010101: sbox7_model = 4'd9;
                6'b010110: sbox7_model = 4'd1;
                6'b010111: sbox7_model = 4'd10;
                6'b011000: sbox7_model = 4'd14;
                6'b011001: sbox7_model = 4'd3;
                6'b011010: sbox7_model = 4'd5;
                6'b011011: sbox7_model = 4'd12;
                6'b011100: sbox7_model = 4'd2;
                6'b011101: sbox7_model = 4'd15;
                6'b011110: sbox7_model = 4'd8;
                6'b011111: sbox7_model = 4'd6;
                6'b100000: sbox7_model = 4'd1;
                6'b100001: sbox7_model = 4'd4;
                6'b100010: sbox7_model = 4'd11;
                6'b100011: sbox7_model = 4'd13;
                6'b100100: sbox7_model = 4'd12;
                6'b100101: sbox7_model = 4'd3;
                6'b100110: sbox7_model = 4'd7;
                6'b100111: sbox7_model = 4'd14;
                6'b101000: sbox7_model = 4'd10;
                6'b101001: sbox7_model = 4'd15;
                6'b101010: sbox7_model = 4'd6;
                6'b101011: sbox7_model = 4'd8;
                6'b101100: sbox7_model = 4'd0;
                6'b101101: sbox7_model = 4'd5;
                6'b101110: sbox7_model = 4'd9;
                6'b101111: sbox7_model = 4'd2;
                6'b110000: sbox7_model = 4'd6;
                6'b110001: sbox7_model = 4'd11;
                6'b110010: sbox7_model = 4'd13;
                6'b110011: sbox7_model = 4'd8;
                6'b110100: sbox7_model = 4'd1;
                6'b110101: sbox7_model = 4'd4;
                6'b110110: sbox7_model = 4'd10;
                6'b110111: sbox7_model = 4'd7;
                6'b111000: sbox7_model = 4'd9;
                6'b111001: sbox7_model = 4'd5;
                6'b111010: sbox7_model = 4'd0;
                6'b111011: sbox7_model = 4'd15;
                6'b111100: sbox7_model = 4'd14;
                6'b111101: sbox7_model = 4'd2;
                6'b111110: sbox7_model = 4'd3;
                6'b111111: sbox7_model = 4'd12;
                default:   sbox7_model = 4'd0;
            endcase
        end
    endfunction

    // BSout must match the defined S-box lookup for Bin.
    check_sbox7_lookup_table: assert property (
        @(posedge clk) BSout == sbox7_model(Bin)
    );

    // With no state, a stable Bin must keep BSout stable.
    check_stable_bin_implies_stable_bsout: assert property (
        @(posedge clk) $stable(Bin) |-> $stable(BSout)
    );

endmodule