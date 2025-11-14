
module tlu_prencoder16 (din, dout);

input [15:0] din;
output [3:0] dout;

wire [15:0] onehot;

genvar i;
generate
  for (i = 0; i < 16; i = i + 1) begin
    assign onehot[i] = din[i] & ~(|din[i-1:0]);
  end
endgenerate

assign dout[3] = |onehot[15:8];
assign dout[2] = (|onehot[7:4]) | (|onehot[15:12]);
assign dout[1] = (|onehot[3:2]) | (|onehot[7:6]) | (|onehot[11:10]) | (|onehot[15:14]);
assign dout[0] = onehot[0] | onehot[1] | onehot[3] | onehot[5] | onehot[7] | onehot[9] | onehot[11] | onehot[13] | onehot[15];

endmodule