module binary_counter
#(parameter MAX_COUNT=15)
(
  input clk,
  input reset,
  output reg [3:0]count,  // 4 bits for 16 counts
  output reg overflow
);

  always @(posedge clk or posedge reset)
  begin
    if (reset)
    begin
      count <= 0;
      overflow <= 0;
    end
    else if (count == MAX_COUNT)
    begin
      count <= 0;
      overflow <= 1;
    end
    else
    begin
      count <= count + 1;
      overflow <= 0;
    end
  end

endmodule