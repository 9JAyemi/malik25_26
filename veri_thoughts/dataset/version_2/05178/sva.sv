module sbox1_sva (
    input logic       clk,
    input logic [6:1] Bin,
    input logic [4:1] BSout
);

    logic [6:1] offset;

    assign offset = {Bin[6], Bin[1], Bin[5:2]};

    function automatic logic [4:1] expected_bsout(input logic [6:1] off);
        begin
            case (off)
                6'b000000: expected_bsout = 4'd14;
                6'b000001: expected_bsout = 4'd4;
                6'b000010: expected_bsout = 4'd13;
                6'b000011: expected_bsout = 4'd1;
                6'b000100: expected_bsout = 4'd2;
                6'b000101: expected_bsout = 4'd15;
                6'b000110: expected_bsout = 4'd11;
                6'b000111: expected_bsout = 4'd8;
                6'b001000: expected_bsout = 4'd3;
                6'b001001: expected_bsout = 4'd10;
                6'b001010: expected_bsout = 4'd6;
                6'b001011: expected_bsout = 4'd12;
                6'b001100: expected_bsout = 4'd5;
                6'b001101: expected_bsout = 4'd9;
                6'b001110: expected_bsout = 4'd0;
                6'b001111: expected_bsout = 4'd7;
                6'b010000: expected_bsout = 4'd0;
                6'b010001: expected_bsout = 4'd15;
                6'b010010: expected_bsout = 4'd7;
                6'b010011: expected_bsout = 4'd4;
                6'b010100: expected_bsout = 4'd14;
                6'b010101: expected_bsout = 4'd2;
                6'b010110: expected_bsout = 4'd13;
                6'b010111: expected_bsout = 4'd1;
                6'b011000: expected_bsout = 4'd10;
                6'b011001: expected_bsout = 4'd6;
                6'b011010: expected_bsout = 4'd12;
                6'b011011: expected_bsout = 4'd11;
                6'b011100: expected_bsout = 4'd9;
                6'b011101: expected_bsout = 4'd5;
                6'b011110: expected_bsout = 4'd3;
                6'b011111: expected_bsout = 4'd8;
                6'b100000: expected_bsout = 4'd4;
                6'b100001: expected_bsout = 4'd1;
                6'b100010: expected_bsout = 4'd14;
                6'b100011: expected_bsout = 4'd8;
                6'b100100: expected_bsout = 4'd13;
                6'b100101: expected_bsout = 4'd6;
                6'b100110: expected_bsout = 4'd2;
                6'b100111: expected_bsout = 4'd11;
                6'b101000: expected_bsout = 4'd15;
                6'b101001: expected_bsout = 4'd12;
                6'b101010: expected_bsout = 4'd9;
                6'b101011: expected_bsout = 4'd7;
                6'b101100: expected_bsout = 4'd3;
                6'b101101: expected_bsout = 4'd10;
                6'b101110: expected_bsout = 4'd5;
                6'b101111: expected_bsout = 4'd0;
                6'b110000: expected_bsout = 4'd15;
                6'b110001: expected_bsout = 4'd12;
                6'b110010: expected_bsout = 4'd8;
                6'b110011: expected_bsout = 4'd2;
                6'b110100: expected_bsout = 4'd4;
                6'b110101: expected_bsout = 4'd9;
                6'b110110: expected_bsout = 4'd1;
                6'b110111: expected_bsout = 4'd7;
                6'b111000: expected_bsout = 4'd5;
                6'b111001: expected_bsout = 4'd11;
                6'b111010: expected_bsout = 4'd3;
                6'b111011: expected_bsout = 4'd14;
                6'b111100: expected_bsout = 4'd10;
                6'b111101: expected_bsout = 4'd0;
                6'b111110: expected_bsout = 4'd6;
                6'b111111: expected_bsout = 4'd13;
                default:   expected_bsout = 4'd0;
            endcase
        end
    endfunction

    // BSout must match the implemented S-box lookup on every sampled cycle.
    check_lookup_exact: assert property (
        @(posedge clk) BSout == expected_bsout(offset)
    );

    // Offsets 00xxxx must map to the first table row.
    check_row_00: assert property (
        @(posedge clk) (offset[6:5] == 2'b00) |-> (BSout == expected_bsout(offset))
    );

    // Offsets 01xxxx must map to the second table row.
    check_row_01: assert property (
        @(posedge clk) (offset[6:5] == 2'b01) |-> (BSout == expected_bsout(offset))
    );

    // Offsets 10xxxx must map to the third table row.
    check_row_10: assert property (
        @(posedge clk) (offset[6:5] == 2'b10) |-> (BSout == expected_bsout(offset))
    );

    // Offsets 11xxxx must map to the fourth table row.
    check_row_11: assert property (
        @(posedge clk) (offset[6:5] == 2'b11) |-> (BSout == expected_bsout(offset))
    );

endmodule