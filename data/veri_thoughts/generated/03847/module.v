module simple_adder(
  input [7:0] a,
  input [7:0] b,
  input cin,
  output reg [7:0] sum,
  output reg cout
);

  wire [8:0] temp_sum;
  assign temp_sum = {1'b0, a} + {1'b0, b} + cin;
  
  // Check if overflow occurred
  always @(*) begin
    if (temp_sum[8] == 1) begin
      if (temp_sum[7] == 1) begin
        sum <= 8'b10000000; // -128 in 2's complement
      end else begin
        sum <= 8'b01111111; // 127 in 2's complement
      end
      cout <= 1;
    end else begin
      sum <= temp_sum[7:0];
      cout <= 0;
    end
  end

endmodule