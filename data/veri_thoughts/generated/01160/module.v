module d_ff_en_parameterized #
  (
    parameter WIDTH = 1,
    parameter INIT = 0
  )
  (
    input wire CLK,
    input wire E,
    input wire [WIDTH-1:0] D,
    output reg [WIDTH-1:0] Q
  );

  always @(posedge CLK) begin
    if (E) begin
      Q <= D;
    end
  end

  initial begin
    Q <= INIT;
  end

endmodule