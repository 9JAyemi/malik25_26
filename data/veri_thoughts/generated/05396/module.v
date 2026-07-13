module binary_counter(
  input clk,
  input rst,
  output reg [3:0] out
);

  always @(posedge clk or negedge rst) begin
    if (rst == 0) begin
      out <= 4'b0000;
    end else begin
      out <= out + 1;
    end
  end

endmodule