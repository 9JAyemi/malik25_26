
module BrzVariable_17_1_s0_ (
  write_0r, write_0a, write_0d,
  read_0r, read_0a, read_0d
);
  input write_0r;
  output write_0a;
  input [16:0] write_0d;
  input read_0r;
  output read_0a;
  output [16:0] read_0d;
  reg [16:0] data_0n; 
  wire nWriteReq_0n = ~write_0r;
  wire bWriteReq_0n = 1'b0;
  wire nbWriteReq_0n = 1'b1;

  assign read_0a = read_0r;
  assign read_0d = data_0n;
  assign write_0a = nWriteReq_0n && !bWriteReq_0n && nbWriteReq_0n;
  always @ (posedge write_0r) begin
    if (nWriteReq_0n && !bWriteReq_0n && nbWriteReq_0n) begin
      data_0n <= write_0d; 
    end
  end
endmodule