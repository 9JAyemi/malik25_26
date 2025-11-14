module accumulator #(
  parameter n = 8 // number of bits in binary numbers
)(
  input [n-1:0] data,
  input clk,
  input rst,
  output reg [n-1:0] sum
);


reg [n-1:0] prev_sum; // flip-flop to store previous sum

always @(posedge clk) begin
  if (rst) begin
    sum <= 0; // reset sum to 0
    prev_sum <= 0; // reset previous sum to 0
  end else begin
    prev_sum <= sum; // store previous sum
    sum <= data + prev_sum; // update sum with current data and previous sum
  end
end

endmodule