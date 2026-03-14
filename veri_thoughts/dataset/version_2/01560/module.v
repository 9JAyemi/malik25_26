module binary_counter (
  input clk,
  input reset,
  output reg [2:0] count,
  output reg enable
);

  always @(posedge clk) begin
    if (reset) begin
      count <= 3'b000;
      enable <= 1'b0;
    end
    else begin
      if (count == 3'b101) begin
        count <= 3'b000;
        enable <= 1'b1;
      end
      else begin
        count <= count + 1;
        enable <= 1'b0;
      end
    end
  end

endmodule
