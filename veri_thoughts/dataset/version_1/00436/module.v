
module Multiplexer_AC__parameterized69
   #(parameter WIDTH = 1)
   (input ctrl,
    input [WIDTH-1:0] D0,
    input [WIDTH-1:0] D1,
    output [WIDTH-1:0] S);
  
  wire [WIDTH-1:0] mux_out;
  
  assign mux_out[0] = (ctrl) ? D1[0] : D0[0];
  
  generate
    genvar i;
    for (i = 1; i < WIDTH; i = i + 1) begin : gen_mux
      assign mux_out[i] = (ctrl) ? D1[i] : D0[i];
    end
  endgenerate
  
  assign S = mux_out;
  
endmodule