
module multi_QI
   (CLK,
    reset,
    A,
    B,
    P);
   input CLK;
  input reset;
  input [15:0]A;
  input [15:0]B;
  output reg [31:0]P;

  always @(posedge CLK, posedge reset) begin
    if (reset) begin
      P <= 0;
    end else begin
      P <= A * B;
    end
  end

endmodule