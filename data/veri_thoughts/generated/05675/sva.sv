module HexTo7Segment_assertions (
    input logic clk,
    input logic [3:0] HEXnumber,
    input logic [7:0] Segments
);

    function automatic logic [7:0] expected_segments(input logic [3:0] hex);
        begin
            case (hex)
                4'b0000: expected_segments = 8'b11000000;
                4'b0001: expected_segments = 8'b11111001;
                4'b0010: expected_segments = 8'b10100100;
                4'b0011: expected_segments = 8'b10110000;
                4'b0100: expected_segments = 8'b10011001;
                4'b0101: expected_segments = 8'b10010010;
                4'b0110: expected_segments = 8'b10000010;
                4'b0111: expected_segments = 8'b11111000;
                4'b1000: expected_segments = 8'b10000000;
                4'b1001: expected_segments = 8'b10010000;
                4'b1010: expected_segments = 8'b10001000;
                4'b1011: expected_segments = 8'b10000011;
                4'b1100: expected_segments = 8'b11000110;
                4'b1101: expected_segments = 8'b10100001;
                4'b1110: expected_segments = 8'b10000110;
                4'b1111: expected_segments = 8'b10001110;
                default: expected_segments = 8'b00000000;
            endcase
        end
    endfunction

    // Segments must match the RTL decode table for the sampled HEXnumber.
    check_hex_to_7segment_decode: assert property (
        @(posedge clk) Segments === expected_segments(HEXnumber)
    );

endmodule