module adder_4bit (
  input [3:0] A,
  input [3:0] B,
  input CIN,
  input CLK,
  input RST,
  output [3:0] SUM,
  output COUT
);

  reg [3:0] SUM_reg;
  reg COUT_reg;

  always @(posedge CLK, negedge RST) begin
    if (~RST) begin
      SUM_reg <= 4'b0;
      COUT_reg <= 1'b0;
    end else begin
      SUM_reg <= A + B + CIN;
      COUT_reg <= (A[3] & B[3]) | (A[3] & CIN) | (B[3] & CIN);
    end
  end

  assign SUM = SUM_reg;
  assign COUT = COUT_reg;

endmodule