
module DelayTest(
    input clk,
    input reset,
    input [3:0] data,
    output reg [3:0] out1,
    output reg [3:0] out2,
    output reg [3:0] out3
);

  // Test different delays.
  always @(posedge clk) begin
    if (reset) begin
      out1 <= 0;
      out2 <= 0;
      out3 <= 0;
    end else begin
      out1 <= data;
      out2 <= out1;
      out3 <= out2;
    end
  end

endmodule