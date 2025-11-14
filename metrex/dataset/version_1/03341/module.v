
module mux
   #(parameter N = 1)
   (input ctrl,
    input [N-1:0] D0,
    input [N-1:0] D1,
    output [N-1:0] S);

  wire [N-1:0] S;
  assign S = (ctrl == 1'b0) ? D0 : D1;

endmodule