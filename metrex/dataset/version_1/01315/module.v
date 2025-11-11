
module top_module (
    input [15:0] A,
    input [15:0] B,
    input [3:0] S,
    input [3:0] input_bcd,
    output [7:0] final_output
);

    wire [15:0] barrel_shifter_output;
    wire [7:0] bcd_converter_output;
    
    assign barrel_shifter_output = (S == 4'b0000) ? A :
                                   (S == 4'b0001) ? A << 1 :
                                   (S == 4'b0010) ? A << 2 :
                                   (S == 4'b0011) ? A << 3 :
                                   (S == 4'b0100) ? A << 4 :
                                   (S == 4'b0101) ? A << 5 :
                                   (S == 4'b0110) ? A << 6 :
                                   (S == 4'b0111) ? A << 7 :
                                   (S == 4'b1000) ? A << 8 :
                                   (S == 4'b1001) ? A << 9 :
                                   (S == 4'b1010) ? A << 10 :
                                   (S == 4'b1011) ? A << 11 :
                                   (S == 4'b1100) ? A << 12 :
                                   (S == 4'b1101) ? A << 13 :
                                   (S == 4'b1110) ? A << 14 :
                                   (S == 4'b1111) ? A << 15 : 16'b0;

    assign bcd_converter_output = (input_bcd == 4'b0000) ? 8'b00000000 :
                                  (input_bcd == 4'b0001) ? 8'b00000001 :
                                  (input_bcd == 4'b0010) ? 8'b00000010 :
                                  (input_bcd == 4'b0011) ? 8'b00000011 :
                                  (input_bcd == 4'b0100) ? 8'b00000100 :
                                  (input_bcd == 4'b0101) ? 8'b00000101 :
                                  (input_bcd == 4'b0110) ? 8'b00000110 :
                                  (input_bcd == 4'b0111) ? 8'b00000111 :
                                  (input_bcd == 4'b1000) ? 8'b00001000 :
                                  (input_bcd == 4'b1001) ? 8'b00001001 :
                                  (input_bcd == 4'b1010) ? 8'b00001010 :
                                  (input_bcd == 4'b1011) ? 8'b00001011 :
                                  (input_bcd == 4'b1100) ? 8'b00001100 :
                                  (input_bcd == 4'b1101) ? 8'b00001101 :
                                  (input_bcd == 4'b1110) ? 8'b00001110 :
                                  8'b00000000;

    assign final_output = barrel_shifter_output[15:8] + bcd_converter_output[7:0];
    
endmodule
module barrel_shifter (
    input [15:0] A,
    input [15:0] B,
    input [3:0] S,
    output [15:0] Y
);

    assign Y = (S == 4'b0000) ? A :
               (S == 4'b0001) ? A << 1 :
               (S == 4'b0010) ? A << 2 :
               (S == 4'b0011) ? A << 3 :
               (S == 4'b0100) ? A << 4 :
               (S == 4'b0101) ? A << 5 :
               (S == 4'b0110) ? A << 6 :
               (S == 4'b0111) ? A << 7 :
               (S == 4'b1000) ? A << 8 :
               (S == 4'b1001) ? A << 9 :
               (S == 4'b1010) ? A << 10 :
               (S == 4'b1011) ? A << 11 :
               (S == 4'b1100) ? A << 12 :
               (S == 4'b1101) ? A << 13 :
               (S == 4'b1110) ? A << 14 :
               (S == 4'b1111) ? A << 15 : 16'b0;

endmodule