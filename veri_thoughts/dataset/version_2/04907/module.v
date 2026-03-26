module edge_detect(
  input               clk,
  input               rst_n,
  input               a,
  output reg          rise,
  output reg          fall
);

  reg a_prev;

  always @(posedge clk or negedge rst_n) begin
    if (~rst_n) begin
      a_prev <= 1'b0;
      rise <= 1'b0;
      fall <= 1'b0;
    end
    else begin
      a_prev <= a;
      if (a == 1'b1 && a_prev == 1'b0) begin
        rise <= 1'b1;
        fall <= 1'b0;
      end
      else if (a == 1'b0 && a_prev == 1'b1) begin
        rise <= 1'b0;
        fall <= 1'b1;
      end
      else begin
        rise <= 1'b0;
        fall <= 1'b0;
      end
    end
  end

endmodule