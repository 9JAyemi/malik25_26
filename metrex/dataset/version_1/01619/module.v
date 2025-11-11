
module clock_divider (
  input clk,
  input reset,
  output reg locked,
  output reg clk_out1,
  output reg clk_out2,
  output reg clk_out3
);

  reg [23:0] count = 0;
  reg [23:0] limit1 = 24'd10_000_000;
  reg [23:0] limit2 = 24'd5_000_000;
  reg [23:0] limit3 = 24'd2_500_000;

  always @(posedge clk or posedge reset) begin
    if (reset) begin
      count <= 0;
      clk_out1 <= 0;
      locked <= 0;
    end else begin
      count <= count + 1;
      if (count == limit1) begin
        clk_out1 <= ~clk_out1;
      end
      if (count == limit2) begin
        clk_out2 <= ~clk_out2;
      end
      if (count == limit3) begin
        clk_out3 <= ~clk_out3;
      end
      if (count == 0) begin
        locked <= 1;
      end else if (count == limit1/2) begin
        locked <= (clk_out1 == clk);
      end else if (count == limit2/2) begin
        locked <= (clk_out2 == clk);
      end else if (count == limit3/2) begin
        locked <= (clk_out3 == clk);
      end
    end
  end

endmodule