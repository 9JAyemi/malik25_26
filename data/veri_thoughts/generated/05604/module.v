

`ifndef LIB_DFF_V_
`define LIB_DFF_V_


module dff#(
    parameter WIDTH = 1
  ) (
    input wire clk,
    input wire rst,

    input wire [WIDTH-1:0] inp,
    output reg [WIDTH-1:0] outp
  );

  always @(posedge clk) begin
    outp <= rst ? 0 : inp;
  end

endmodule

`endif 