module Multiplexer #(parameter INIT_VALUE = 8'hB8)
   (input ctrl,
    input [0:0] D0,
    input [0:0] D1,
    output reg [0:0] S);

  wire [0:0] D0_wire;
  wire [0:0] D1_wire;
  wire S_wire;

  assign D0_wire = D0;
  assign D1_wire = D1;

  always @*
  begin
    case(ctrl)
      1'b0: S = D0_wire;
      1'b1: S = D1_wire;
    endcase
  end

endmodule