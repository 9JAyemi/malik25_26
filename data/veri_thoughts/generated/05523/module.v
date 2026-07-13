
module DEMUX (
  input in,
  input [n-1:0] sel,
  output [2**n-1:0] out
);

parameter n = 2; // number of select signals

wire [2**n-1:0] mux_out;

genvar i;
generate
  for (i = 0; i < 2**n; i = i + 1) begin : mux_gen
    assign mux_out[i] = (sel == i) ? in : 1'b0;
  end
endgenerate

assign out = mux_out; // remove the second for loop

endmodule