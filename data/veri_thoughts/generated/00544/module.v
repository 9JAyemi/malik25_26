module up_counter (
  input clk,
  input reset,
  input enable,
  output reg [2:0] count
);

  always @(posedge clk) begin
    if (reset) begin
      count <= 3'b000;
    end else if (enable) begin
      count <= count + 1;
      if (count == 3'b111) begin
        count <= 3'b000;
      end
    end
  end

endmodule
