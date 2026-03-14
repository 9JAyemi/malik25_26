module counter_3bit_sync_reset (
  input clk,
  input reset,
  input ena,
  output reg [2:0] count,
  output reg flag
);

  always @(posedge clk, posedge reset) begin
    if (reset) begin
      count <= 3'b0;
      flag <= 1'b0;
    end
    else if (ena) begin
      if (count == 3'b111) begin
        count <= 3'b0;
        flag <= 1'b1;
      end
      else begin
        count <= count + 1;
        flag <= 1'b0;
      end
    end
  end

endmodule
