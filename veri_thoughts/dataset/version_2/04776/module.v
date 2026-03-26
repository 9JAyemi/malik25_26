
module counter_4bit(
  input clk,
  input set_l,
  output [3:0] count
);

// Register for storing the count value
reg [3:0] count_reg;

// Sequential logic to update the count value
always @(posedge clk or negedge set_l)
  if (!set_l)
    count_reg <= 4'b0;
  else
    count_reg <= count_reg + 4'b1;

// Output the count value
assign count = count_reg;

endmodule