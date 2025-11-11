module pipelined_JC_counter(
  input                clk,
  input                rst_n,
  output reg  [3:0]    Q
);

  reg [3:0] Q1, Q2, Q3, Q4;

  always @(posedge clk or negedge rst_n) begin
    if (~rst_n) begin
      Q1 <= 4'b0000;
      Q2 <= 4'b0000;
      Q3 <= 4'b0000;
      Q4 <= 4'b0000;
      Q  <= 4'b0000;
    end
    else begin
      Q1 <= Q;
      Q2 <= Q1;
      Q3 <= Q2;
      Q4 <= Q3;
      Q  <= ~(Q1 ^ Q2 ^ Q3 ^ Q4);
    end
  end

endmodule