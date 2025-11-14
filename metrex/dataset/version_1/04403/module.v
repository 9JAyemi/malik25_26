
module DEMUX #(
  parameter n = 4 // number of output signals (2^n)
)(
  input in,
  input [clogb2(n)-1:0] sel,
  output [n-1:0] out
);

wire [n-1:0] mux_out;

assign mux_out[0] = in;

genvar i;
generate
  for (i = 1; i < n; i = i + 1) begin
    assign mux_out[i] = (sel == i) ? in : 0; // use conditional operator
  end
endgenerate

// Drive output signals with MUX output
assign out = mux_out;

function integer clogb2;
  input integer number;
  begin
    clogb2 = 0;
    while (number > 0) begin
      number = number >> 1;
      clogb2 = clogb2 + 1;
    end
  end
endfunction

endmodule