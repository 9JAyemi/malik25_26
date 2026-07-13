module mux_3to4_enable (
  input clk,
  input reset,
  input enable,
  input [2:0] A,
  input [2:0] B,
  input [2:0] C,
  output reg [2:0] W,
  output reg [2:0] X,
  output reg [2:0] Y,
  output reg [2:0] Z
);

  always @(posedge clk) begin
    if (reset) begin
      W <= 3'b0;
      X <= 3'b0;
      Y <= 3'b0;
      Z <= 3'b0;
    end else begin
      if (enable) begin
        W <= A;
        X <= B;
        Y <= B;
        Z <= 3'b0;
      end else begin
        W <= 3'b0;
        X <= 3'b0;
        Y <= 3'b0;
        Z <= C;
      end
    end
  end
  
endmodule
