module mux_16to1 (
  input [15:0] in0,
  input [15:0] in1,
  input [15:0] in2,
  input [15:0] in3,
  input [15:0] in4,
  input [15:0] in5,
  input [15:0] in6,
  input [15:0] in7,
  input [15:0] in8,
  input [15:0] in9,
  input [15:0] in10,
  input [15:0] in11,
  input [15:0] in12,
  input [15:0] in13,
  input [15:0] in14,
  input [15:0] in15,
  input [4:0] sel,
  output reg [31:0] out
);

  always @(*) begin
    case (sel)
      5'b00000: out = in0;
      5'b00001: out = in1;
      5'b00010: out = in2;
      5'b00011: out = in3;
      5'b00100: out = in4;
      5'b00101: out = in5;
      5'b00110: out = in6;
      5'b00111: out = in7;
      5'b01000: out = in8;
      5'b01001: out = in9;
      5'b01010: out = in10;
      5'b01011: out = in11;
      5'b01100: out = in12;
      5'b01101: out = in13;
      5'b01110: out = in14;
      5'b01111: out = in15;
      default: out = 32'b0;
    endcase
  end

endmodule
