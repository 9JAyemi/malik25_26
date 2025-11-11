
module DEMUX #(
  parameter n = 2
)(
  input in,
  input [n-1:0] ctrl,
  output reg [2**n-1:0] out
);

wire [2**n-1:0] mux_out;

assign mux_out[0] = in; // default output

// decode control signal and route input signal to appropriate output
genvar i;
generate
  for (i = 0; i < 2**n; i = i + 1) begin : mux_gen
    always @(*) begin
      if (ctrl == i) out[i] <= in;
      else out[i] <= 1'b0;
    end
  end
endgenerate

endmodule