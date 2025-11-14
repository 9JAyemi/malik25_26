
module decoder_0 (
  input [k-1:0] in,
  output reg [2**k-1:0] out
);

parameter k = 3; // number of control signals

always @(*) begin
  case (in)
    0: out = 8'b00000001;
    1: out = 8'b00000010;
    2: out = 8'b00000100;
    3: out = 8'b00001000;
    4: out = 8'b00010000;
    5: out = 8'b00100000;
    6: out = 8'b01000000;
    7: out = 8'b10000000;
    default: out = 8'b0;
  endcase
end

endmodule
module DEMUX (
  input in,
  input [k-1:0] c,
  output reg [2**k-1:0] out
);

parameter k = 3; // number of control signals

always @(*) begin
  case (c)
    0: out = {in, 3'b000};
    1: out = {in, 3'b001};
    2: out = {in, 3'b010};
    3: out = {in, 3'b011};
    4: out = {in, 3'b100};
    5: out = {in, 3'b101};
    6: out = {in, 3'b110};
    7: out = {in, 3'b111};
    default: out = 8'b0;
  endcase
end

endmodule
module decoder_1 (
  input [k-1:0] in,
  output reg [2**k-1:0] out
);

parameter k = 3; // number of control signals

always @(*) begin
  case (in)
    0: out = 8'b00000001;
    1: out = 8'b00000010;
    2: out = 8'b00000100;
    3: out = 8'b00001000;
    4: out = 8'b00010000;
    5: out = 8'b00100000;
    6: out = 8'b01000000;
    7: out = 8'b10000000;
    default: out = 8'b0;
  endcase
end

endmodule