module DEMUX (
  input in,
  input [1:0] sel,
  output reg [3:0] out
);

parameter n = 2; // number of select bits
parameter m = 4; // number of output signals (2^n)

// Implement the decoding logic using a case statement
always @(*) begin
  case(sel)
    2'b00: out = {in, 3'b000};
    2'b01: out = {3'b000, in};
    2'b10: out = {2'b00, in, 1'b0};
    2'b11: out = {1'b0, in, 2'b00};
    default: out = 4'b0000; // set all output lines to 0 if sel is out of range
  endcase
end

endmodule