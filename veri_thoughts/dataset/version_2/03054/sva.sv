module sbox2_sva (
    input logic clk,
    input logic [6:1] Bin,
    input logic [4:1] BSout
);

    // RTL is combinational with no native clock or reset; clk is a sampling clock.

    function automatic logic [4:1] sbox2_row00(input logic [3:0] col);
        begin
            case (col)
                4'h0: sbox2_row00 = 4'd15;
                4'h1: sbox2_row00 = 4'd1;
                4'h2: sbox2_row00 = 4'd8;
                4'h3: sbox2_row00 = 4'd14;
                4'h4: sbox2_row00 = 4'd6;
                4'h5: sbox2_row00 = 4'd11;
                4'h6: sbox2_row00 = 4'd3;
                4'h7: sbox2_row00 = 4'd4;
                4'h8: sbox2_row00 = 4'd9;
                4'h9: sbox2_row00 = 4'd7;
                4'hA: sbox2_row00 = 4'd2;
                4'hB: sbox2_row00 = 4'd13;
                4'hC: sbox2_row00 = 4'd12;
                4'hD: sbox2_row00 = 4'd0;
                4'hE: sbox2_row00 = 4'd5;
                4'hF: sbox2_row00 = 4'd10;
                default: sbox2_row00 = 4'd0;
            endcase
        end
    endfunction

    function automatic logic [4:1] sbox2_row01(input logic [3:0] col);
        begin
            case (col)
                4'h0: sbox2_row01 = 4'd3;
                4'h1: sbox2_row01 = 4'd13;
                4'h2: sbox2_row01 = 4'd4;
                4'h3: sbox2_row01 = 4'd7;
                4'h4: sbox2_row01 = 4'd15;
                4'h5: sbox2_row01 = 4'd2;
                4'h6: sbox2_row01 = 4'd8;
                4'h7: sbox2_row01 = 4'd14;
                4'h8: sbox2_row01 = 4'd12;
                4'h9: sbox2_row01 = 4'd0;
                4'hA: sbox2_row01 = 4'd1;
                4'hB: sbox2_row01 = 4'd10;
                4'hC: sbox2_row01 = 4'd6;
                4'hD: sbox2_row01 = 4'd9;
                4'hE: sbox2_row01 = 4'd11;
                4'hF: sbox2_row01 = 4'd5;
                default: sbox2_row01 = 4'd0;
            endcase
        end
    endfunction

    function automatic logic [4:1] sbox2_row10(input logic [3:0] col);
        begin
            case (col)
                4'h0: sbox2_row10 = 4'd0;
                4'h1: sbox2_row10 = 4'd14;
                4'h2: sbox2_row10 = 4'd7;
                4'h3: sbox2_row10 = 4'd11;
                4'h4: sbox2_row10 = 4'd10;
                4'h5: sbox2_row10 = 4'd4;
                4'h6: sbox2_row10 = 4'd13;
                4'h7: sbox2_row10 = 4'd1;
                4'h8: sbox2_row10 = 4'd5;
                4'h9: sbox2_row10 = 4'd8;
                4'hA: sbox2_row10 = 4'd12;
                4'hB: sbox2_row10 = 4'd6;
                4'hC: sbox2_row10 = 4'd9;
                4'hD: sbox2_row10 = 4'd3;
                4'hE: sbox2_row10 = 4'd2;
                4'hF: sbox2_row10 = 4'd15;
                default: sbox2_row10 = 4'd0;
            endcase
        end
    endfunction

    function automatic logic [4:1] sbox2_row11(input logic [3:0] col);
        begin
            case (col)
                4'h0: sbox2_row11 = 4'd13;
                4'h1: sbox2_row11 = 4'd8;
                4'h2: sbox2_row11 = 4'd10;
                4'h3: sbox2_row11 = 4'd1;
                4'h4: sbox2_row11 = 4'd3;
                4'h5: sbox2_row11 = 4'd15;
                4'h6: sbox2_row11 = 4'd4;
                4'h7: sbox2_row11 = 4'd2;
                4'h8: sbox2_row11 = 4'd11;
                4'h9: sbox2_row11 = 4'd6;
                4'hA: sbox2_row11 = 4'd7;
                4'hB: sbox2_row11 = 4'd12;
                4'hC: sbox2_row11 = 4'd0;
                4'hD: sbox2_row11 = 4'd5;
                4'hE: sbox2_row11 = 4'd14;
                4'hF: sbox2_row11 = 4'd9;
                default: sbox2_row11 = 4'd0;
            endcase
        end
    endfunction

    function automatic logic [4:1] sbox2_expected(input logic [6:1] bin);
        begin
            case ({bin[6], bin[1]})
                2'b00: sbox2_expected = sbox2_row00(bin[5:2]);
                2'b01: sbox2_expected = sbox2_row01(bin[5:2]);
                2'b10: sbox2_expected = sbox2_row10(bin[5:2]);
                2'b11: sbox2_expected = sbox2_row11(bin[5:2]);
                default: sbox2_expected = 4'd0;
            endcase
        end
    endfunction

    // Full S-box lookup matches the RTL case table.
    check_full_lookup_table: assert property (
        @(posedge clk) BSout === sbox2_expected(Bin)
    );

    // Row 00 entries match the first 16 case items.
    check_row_00_mapping: assert property (
        @(posedge clk) ({Bin[6], Bin[1]} === 2'b00) |-> (BSout === sbox2_row00(Bin[5:2]))
    );

    // Row 01 entries match the second 16 case items.
    check_row_01_mapping: assert property (
        @(posedge clk) ({Bin[6], Bin[1]} === 2'b01) |-> (BSout === sbox2_row01(Bin[5:2]))
    );

    // Row 10 entries match the third 16 case items.
    check_row_10_mapping: assert property (
        @(posedge clk) ({Bin[6], Bin[1]} === 2'b10) |-> (BSout === sbox2_row10(Bin[5:2]))
    );

    // Row 11 entries match the fourth 16 case items.
    check_row_11_mapping: assert property (
        @(posedge clk) ({Bin[6], Bin[1]} === 2'b11) |-> (BSout === sbox2_row11(Bin[5:2]))
    );

    // A stable input must preserve the same output across samples.
    check_output_stable_when_input_stable: assert property (
        @(posedge clk) (Bin === $past(Bin)) |-> (BSout === $past(BSout))
    );

endmodule