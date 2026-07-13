module CRC5_D5_solution(
  nextCRC5_D5,
  Data,
  crc
);

  // polynomial: x^5 + x^2 + 1
  // data width: 5
  // convention: the first serial bit is D[4]
  output reg [4:0] nextCRC5_D5;  // Fix: declare nextCRC5_D5 as reg
  input [4:0] Data;
  input [4:0] crc;
  reg [4:0] d;
  reg [4:0] c;
  reg [4:0] newcrc;

  always @ (Data or crc) begin
    d = Data;
    c = crc;

    newcrc[0] = d[3] ^ d[0] ^ c[0] ^ c[3];
    newcrc[1] = d[4] ^ d[1] ^ c[1] ^ c[4];
    newcrc[2] = d[3] ^ d[2] ^ d[0] ^ c[0] ^ c[2] ^ c[3];
    newcrc[3] = d[4] ^ d[3] ^ d[1] ^ c[1] ^ c[3] ^ c[4];
    newcrc[4] = d[4] ^ d[2] ^ c[2] ^ c[4];

    nextCRC5_D5 = newcrc;  // Fix: use non-blocking assignment for output
  end
endmodule