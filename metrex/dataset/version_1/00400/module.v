
module ctrl_module(
  input [3:0] in,
  input [1:0] ctrl,
  output reg [3:0] out
);

  reg [2:0] index;
  always @* begin
    index = {ctrl, in[1:0]};
  end

  // Implement the output using a case statement
  always @* begin
    case (index)
      3'b000: out = 4'b0000;
      3'b001: out = 4'b1010;
      3'b010: out = 4'b0101;
      3'b011: out = 4'b1111;
      3'b100: out = 4'b1110;
      3'b101: out = 4'b0101;
      3'b110: out = 4'b1010;
      3'b111: out = 4'b0000;
    endcase
  end

endmodule