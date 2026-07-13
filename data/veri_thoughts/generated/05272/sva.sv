module D2STR_B_sva #(
    parameter integer len = 16
) (
    input logic [127:0] str,
    input logic [len-1:0] d
);

    function automatic logic [127:0] bin_string(input logic [len-1:0] d_in);
        integer j;
        begin
            for (j = 0; j < len; j = j + 1) begin
                bin_string[8*j+7:8*j] = d_in[j] ? "1" : "0";
            end
            for (j = len; j < 16; j = j + 1) begin
                bin_string[8*j+7:8*j] = " ";
            end
        end
    endfunction

    // str is the combinational ASCII rendering of d with space padding above len.
    check_binary_string_map: assert property (
        @($global_clock) str == bin_string(d)
    );

endmodule


module D2STR_H_sva #(
    parameter integer len = 16
) (
    input logic        GCLK,
    input logic [127:0] str,
    input logic [4*len-1:0] d
);

    function automatic logic [7:0] hex_char(input logic [3:0] nibble);
        begin
            case (nibble)
                4'd0:  hex_char = "0";
                4'd1:  hex_char = "1";
                4'd2:  hex_char = "2";
                4'd3:  hex_char = "3";
                4'd4:  hex_char = "4";
                4'd5:  hex_char = "5";
                4'd6:  hex_char = "6";
                4'd7:  hex_char = "7";
                4'd8:  hex_char = "8";
                4'd9:  hex_char = "9";
                4'd10: hex_char = "A";
                4'd11: hex_char = "B";
                4'd12: hex_char = "C";
                4'd13: hex_char = "D";
                4'd14: hex_char = "E";
                4'd15: hex_char = "F";
                default: hex_char = " ";
            endcase
        end
    endfunction

    function automatic logic [127:0] hex_string(input logic [4*len-1:0] d_in);
        integer j;
        begin
            for (j = 0; j < len; j = j + 1) begin
                hex_string[8*j+7:8*j] = hex_char(d_in[4*j+3:4*j]);
            end
            for (j = len; j < 16; j = j + 1) begin
                hex_string[8*j+7:8*j] = " ";
            end
        end
    endfunction

    // Each GCLK edge updates str to the hex rendering of the prior sampled d value.
    check_hex_string_update: assert property (
        @(posedge GCLK) 1'b1 |=> str == hex_string($past(d))
    );

endmodule


module D2STR_D_sva #(
    parameter integer len = 4
) (
    input logic        GCLK,
    input logic [127:0] str,
    input logic [4*len-1:0] d
);

    function automatic logic [7:0] dec_char(input logic [3:0] nibble);
        begin
            case (nibble)
                4'd0:  dec_char = "0";
                4'd1:  dec_char = "1";
                4'd2:  dec_char = "2";
                4'd3:  dec_char = "3";
                4'd4:  dec_char = "4";
                4'd5:  dec_char = "5";
                4'd6:  dec_char = "6";
                4'd7:  dec_char = "7";
                4'd8:  dec_char = "8";
                4'd9:  dec_char = "9";
                4'd10: dec_char = " ";
                4'd11: dec_char = " ";
                4'd12: dec_char = " ";
                4'd13: dec_char = " ";
                4'd14: dec_char = " ";
                4'd15: dec_char = "-";
                default: dec_char = " ";
            endcase
        end
    endfunction

    function automatic logic [127:0] dec_string(input logic [4*len-1:0] d_in);
        integer j;
        begin
            for (j = 0; j < len; j = j + 1) begin
                dec_string[8*j+7:8*j] = dec_char(d_in[4*j+3:4*j]);
            end
            for (j = len; j < 16; j = j + 1) begin
                dec_string[8*j+7:8*j] = " ";
            end
        end
    endfunction

    // Each GCLK edge updates str to the decimal-style rendering of the prior sampled d value.
    check_decimal_string_update: assert property (
        @(posedge GCLK) 1'b1 |=> str == dec_string($past(d))
    );

endmodule