module seven_segment_display
(
  input clk,
  input [15:0]num_in,
  output reg [6:0]dig,
  output reg dp,
  output reg neg,
  output reg clr,
  output reg [3:0]dig_sel
);

reg [6:0]dig1;
reg [6:0]dig2;
reg [6:0]dig3;
reg [6:0]dig4;

reg [19:0] clk_div;

always @(posedge clk) begin
  clk_div = clk_div + 1;
end

always @(posedge clk) begin
  if (clk_div == 0)
  begin
    if(dig_sel == 0)
      dig_sel <= 1;
    else
      dig_sel <= {dig_sel[0],dig_sel[3:1]};

    case(dig_sel)
      4'b0010: dig <= dig4;
      4'b0100: dig <= dig3;
      4'b1000: dig <= dig2;
      4'b0001: dig <= dig1;
    endcase
  end
end

always @(posedge clk) begin
  case(num_in[3:0])
    4'b0000: dig1 = 7'b1000000; //0
    4'b0001: dig1 = 7'b1111001; //1
    4'b0010: dig1 = 7'b0100100; //2
    4'b0011: dig1 = 7'b0110000; //3
    4'b0100: dig1 = 7'b0011001; //4
    4'b0101: dig1 = 7'b0010010; //5
    4'b0110: dig1 = 7'b0000010; //6
    4'b0111: dig1 = 7'b1111000; //7
    4'b1000: dig1 = 7'b0000000; //8
    4'b1001: dig1 = 7'b0010000; //9
    4'b1010: dig1 = 7'b0001000; //A
    4'b1011: dig1 = 7'b0000011; //b
    4'b1100: dig1 = 7'b1000110; //C
    4'b1101: dig1 = 7'b0100001; //d
    4'b1110: dig1 = 7'b0000110; //E
    4'b1111: dig1 = 7'b0001110; //F
  endcase
  case(num_in[7:4])
    4'b0000: dig2 = 7'b1000000; //0
    4'b0001: dig2 = 7'b1111001; //1
    4'b0010: dig2 = 7'b0100100; //2
    4'b0011: dig2 = 7'b0110000; //3
    4'b0100: dig2 = 7'b0011001; //4
    4'b0101: dig2 = 7'b0010010; //5
    4'b0110: dig2 = 7'b0000010; //6
    4'b0111: dig2 = 7'b1111000; //7
    4'b1000: dig2 = 7'b0000000; //8
    4'b1001: dig2 = 7'b0010000; //9
    4'b1010: dig2 = 7'b0001000; //A
    4'b1011: dig2 = 7'b0000011; //b
    4'b1100: dig2 = 7'b1000110; //C
    4'b1101: dig2 = 7'b0100001; //d
    4'b1110: dig2 = 7'b0000110; //E
    4'b1111: dig2 = 7'b0001110; //F
  endcase
  case(num_in[11:8])
    4'b0000: dig3 = 7'b1000000; //0
    4'b0001: dig3 = 7'b1111001; //1
    4'b0010: dig3 = 7'b0100100; //2
    4'b0011: dig3 = 7'b0110000; //3
    4'b0100: dig3 = 7'b0011001; //4
    4'b0101: dig3 = 7'b0010010; //5
    4'b0110: dig3 = 7'b0000010; //6
    4'b0111: dig3 = 7'b1111000; //7
    4'b1000: dig3 = 7'b0000000; //8
    4'b1001: dig3 = 7'b0010000; //9
    4'b1010: dig3 = 7'b0001000; //A
    4'b1011: dig3 = 7'b0000011; //b
    4'b1100: dig3 = 7'b1000110; //C
    4'b1101: dig3 = 7'b0100001; //d
    4'b1110: dig3 = 7'b0000110; //E
    4'b1111: dig3 = 7'b0001110; //F
  endcase
  case(num_in[15:12])
    4'b0000: dig4 = 7'b1000000; //0
    4'b0001: dig4 = 7'b1111001; //1
    4'b0010: dig4 = 7'b0100100; //2
    4'b0011: dig4 = 7'b0110000; //3
    4'b0100: dig4 = 7'b0011001; //4
    4'b0101: dig4 = 7'b0010010; //5
    4'b0110: dig4 = 7'b0000010; //6
    4'b0111: dig4 = 7'b1111000; //7
    4'b1000: dig4 = 7'b0000000; //8
    4'b1001: dig4 = 7'b0010000; //9
    4'b1010: dig4 = 7'b0001000; //A
    4'b1011: dig4 = 7'b0000011; //b
    4'b1100: dig4 = 7'b1000110; //C
    4'b1101: dig4 = 7'b0100001; //d
    4'b1110: dig4 = 7'b0000110; //E
    4'b1111: dig4 = 7'b0001110; //F
  endcase
end

always @(posedge clk) begin
  dp <= 0;
  neg <= 0;
  clr <= 0;
end

endmodule