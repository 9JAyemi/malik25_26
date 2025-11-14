
module Multiplexer_AC__parameterized33
   (ctrl,
    D0,
    D1,
    D2,
    S);
  input ctrl;
  input [0:0]D0;
  input [0:0]D1;
  input [0:0]D2;
  output [0:0]S;

  wire [0:0]S;
  wire [2:0]sel;

  assign sel = {ctrl, ctrl};

  assign S = (sel == 3'b000) ? D0 : 
             (sel == 3'b001) ? D1 : 
             (sel == 3'b010) ? D2 : 0;

endmodule
