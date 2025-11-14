module up_down_counter (
  input clk,
  input reset,
  input up_down,
  input enable,
  output reg [3:0] count
);

  always @(posedge clk, posedge reset) begin
    if (reset) begin
      count <= 4'b0000;
    end else if (enable) begin
      if (up_down) begin
        if (count == 4'b1111) begin
          count <= 4'b0000;
        end else begin
          count <= count + 1;
        end
      end else begin
        if (count == 4'b0000) begin
          count <= 4'b1111;
        end else begin
          count <= count - 1;
        end
      end
    end
  end

endmodule
