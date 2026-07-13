module counter_4bit(
  input clk, rst, en,
  output reg [3:0] out
);

  always @(posedge clk or negedge rst)
  begin
    if (!rst) // synchronous reset
      out <= 4'b0;
    else if (en) // asynchronous enable
      out <= out + 1;
  end

endmodule