
module crc_module (
  input clk,
  input [63:0] data_in,
  output reg [63:0] checksum
);

  integer cyc = 0;
  reg [63:0] crc;
  wire [1:0] o[3:0]; // declare o as a 4-element array of 2-bit wires

  assign o[0] = {crc[1], crc[0]};
  assign o[1] = {crc[3], crc[2]};
  assign o[2] = {crc[5], crc[4]};
  assign o[3] = {crc[7], crc[6]};

  always @ (posedge clk) begin
    cyc <= cyc + 1;
    crc <= {crc[62:0], crc[63] ^ crc[2] ^ crc[0]};
    if (cyc == 0) begin
      crc <= 64'h5aef0c8d_d70a4497;
    end
    else if (cyc >= 90) begin
      checksum <= {32'h0, 6'h0, o[3], 6'h0, o[2], 6'h0, o[1], 6'h0, o[0]};
    end
  end

endmodule

module Test (
  input [1:0] i,
  output [1:0] o
);

  assign o = (i == 2'b00) ? 2'b00 :
             (i == 2'b01) ? 2'b11 :
             (i == 2'b10) ? 2'b01 :
             (i == 2'b11) ? 2'b10 :
             2'bx;

endmodule
