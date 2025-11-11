
module adder_comparator (
  input clk,
  input reset,
  input [3:0] input1,
  input [3:0] input2,
  output reg [3:0] sum,  // Declare sum as a register
  output reg [1:0] comparison_result
);

reg [3:0] adder_output;

always @(posedge clk) begin
  if (reset) begin
    adder_output <= 4'b0;
    comparison_result <= 2'b0;
  end else begin
    adder_output <= input1 + input2;
    sum <= adder_output; // Assign the value of adder_output to sum
    
    if (adder_output[3:2] > 2'b10) begin
      comparison_result <= 2'b10; // greater than
    end else if (adder_output[3:2] == 2'b10) begin
      comparison_result <= 2'b01; // equal to
    end else begin
      comparison_result <= 2'b00; // less than
    end
  end
end

endmodule
