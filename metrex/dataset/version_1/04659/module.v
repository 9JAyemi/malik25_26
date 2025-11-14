
module CRC (
  input [n-1:0] in,
  output reg [m-1:0] out,
  input clk
);

parameter n = 8; // number of input bits
parameter m = 16; // number of output bits
parameter k = 16; // degree of the generator polynomial

reg [k-1:0] crc_reg;

// Generator polynomial
reg [k-1:0] gen_poly = {1'b1, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0, 1'b0, 1'b1};

// CRC generator
integer i;
always @(posedge clk) begin
  crc_reg = {in, crc_reg[k-1:n]};
  for (i = 0; i < n; i = i + 1) begin
    if (crc_reg[k-1] == 1'b1) begin
      crc_reg = crc_reg ^ gen_poly;
    end
    crc_reg = crc_reg << 1;
  end
  out <= {in, crc_reg[n-1:0]};
end

endmodule