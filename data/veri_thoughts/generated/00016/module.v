module Multiplexer
    #(parameter N = 1)
    (input [N-1:0] D0,
     input [N-1:0] D1,
     input ctrl,
     output [N-1:0] S);

    wire [N-1:0] temp;

    assign temp = ctrl ? D1 : D0;
    assign S = temp;

endmodule