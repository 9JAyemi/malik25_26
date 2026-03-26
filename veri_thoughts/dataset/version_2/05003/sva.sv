module sbox3_sva (
    input logic       clk,
    input logic [6:1] Bin,
    input logic [4:1] BSout
);

    // sbox3 is combinational and has no RTL clock or reset; clk is only a sampling clock.

    function automatic logic [4:1] expected_bsout(input logic [6:1] bin);
        logic [6:1] offset_v;
        begin
            offset_v = {bin[6], bin[1], bin[5:2]};
            case (offset_v)
                6'b000000: expected_bsout = 4'd10;
                6'b000001: expected_bsout = 4'd0;
                6'b000010: expected_bsout = 4'd9;
                6'b000011: expected_bsout = 4'd14;
                6'b000100: expected_bsout = 4'd6;
                6'b000101: expected_bsout = 4'd3;
                6'b000110: expected_bsout = 4'd15;
                6'b000111: expected_bsout = 4'd5;
                6'b001000: expected_bsout = 4'd1;
                6'b001001: expected_bsout = 4'd13;
                6'b001010: expected_bsout = 4'd12;
                6'b001011: expected_bsout = 4'd7;
                6'b001100: expected_bsout = 4'd11;
                6'b001101: expected_bsout = 4'd4;
                6'b001110: expected_bsout = 4'd2;
                6'b001111: expected_bsout = 4'd8;
                6'b010000: expected_bsout = 4'd13;
                6'b010001: expected_bsout = 4'd7;
                6'b010010: expected_bsout = 4'd0;
                6'b010011: expected_bsout = 4'd9;
                6'b010100: expected_bsout = 4'd3;
                6'b010101: expected_bsout = 4'd4;
                6'b010110: expected_bsout = 4'd6;
                6'b010111: expected_bsout = 4'd10;
                6'b011000: expected_bsout = 4'd2;
                6'b011001: expected_bsout = 4'd8;
                6'b011010: expected_bsout = 4'd5;
                6'b011011: expected_bsout = 4'd14;
                6'b011100: expected_bsout = 4'd12;
                6'b011101: expected_bsout = 4'd11;
                6'b011110: expected_bsout = 4'd15;
                6'b011111: expected_bsout = 4'd1;
                6'b100000: expected_bsout = 4'd13;
                6'b100001: expected_bsout = 4'd6;
                6'b100010: expected_bsout = 4'd4;
                6'b100011: expected_bsout = 4'd9;
                6'b100100: expected_bsout = 4'd8;
                6'b100101: expected_bsout = 4'd15;
                6'b100110: expected_bsout = 4'd3;
                6'b100111: expected_bsout = 4'd0;
                6'b101000: expected_bsout = 4'd11;
                6'b101001: expected_bsout = 4'd1;
                6'b101010: expected_bsout = 4'd2;
                6'b101011: expected_bsout = 4'd12;
                6'b101100: expected_bsout = 4'd5;
                6'b101101: expected_bsout = 4'd10;
                6'b101110: expected_bsout = 4'd14;
                6'b101111: expected_bsout = 4'd7;
                6'b110000: expected_bsout = 4'd1;
                6'b110001: expected_bsout = 4'd10;
                6'b110010: expected_bsout = 4'd13;
                6'b110011: expected_bsout = 4'd0;
                6'b110100: expected_bsout = 4'd6;
                6'b110101: expected_bsout = 4'd9;
                6'b110110: expected_bsout = 4'd8;
                6'b110111: expected_bsout = 4'd7;
                6'b111000: expected_bsout = 4'd4;
                6'b111001: expected_bsout = 4'd15;
                6'b111010: expected_bsout = 4'd14;
                6'b111011: expected_bsout = 4'd3;
                6'b111100: expected_bsout = 4'd11;
                6'b111101: expected_bsout = 4'd5;
                6'b111110: expected_bsout = 4'd2;
                6'b111111: expected_bsout = 4'd12;
                default:   expected_bsout = 4'd0;
            endcase
        end
    endfunction

    // BSout must match the complete lookup table for the current Bin.
    check_full_lookup_table: assert property (
        @(posedge clk) BSout == expected_bsout(Bin)
    );

    // If Bin is unchanged across samples, BSout must also remain unchanged.
    check_stable_input_keeps_output_stable: assert property (
        @(posedge clk) $stable(Bin) |-> $stable(BSout)
    );

    // Offset 000000 must map to 10.
    check_offset_000000_value: assert property (
        @(posedge clk) ({Bin[6], Bin[1], Bin[5:2]} == 6'b000000) |-> (BSout == 4'd10)
    );

    // Offset 011111 must map to 1.
    check_offset_011111_value: assert property (
        @(posedge clk) ({Bin[6], Bin[1], Bin[5:2]} == 6'b011111) |-> (BSout == 4'd1)
    );

    // Offset 100111 must map to 0.
    check_offset_100111_value: assert property (
        @(posedge clk) ({Bin[6], Bin[1], Bin[5:2]} == 6'b100111) |-> (BSout == 4'd0)
    );

    // Offset 111111 must map to 12.
    check_offset_111111_value: assert property (
        @(posedge clk) ({Bin[6], Bin[1], Bin[5:2]} == 6'b111111) |-> (BSout == 4'd12)
    );

endmodule