module RegisterAdd__parameterized5
   #(parameter N = 23)
   (Q,
    E,
    D,
    CLK,
    AR);
  output [N-1:0]Q;
  input [0:0]E;
  input [N-1:0]D;
  input CLK;
  input [0:0]AR;

  wire [0:0]AR;
  wire CLK;
  wire [N-1:0]D;
  wire [0:0]E;
  wire [N-1:0]Q;

  reg [N-1:0]Q_reg;

  always @(posedge CLK or negedge AR)
  begin
    if (!AR) begin
      Q_reg <= {N{1'b0}};
    end
    else if (E) begin
      Q_reg <= D + Q_reg;
    end
  end

  assign Q = Q_reg;

endmodule