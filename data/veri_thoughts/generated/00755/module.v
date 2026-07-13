module mux_1bit (
  input ctrl,
  input [0:0] D0,
  input [0:0] D1,
  output reg [0:0] S
);

  always @(*) begin
    case(ctrl)
      1'b0: S = D0;
      1'b1: S = D1;
    endcase
  end

endmodule