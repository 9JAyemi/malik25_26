module up_down_counter (
  input clk,
  input reset,
  input enable,
  input control,
  output reg [2:0] count
);

  always @(posedge clk, posedge reset) begin
    if (reset) begin
      count <= 3'b0;
    end else if (enable) begin
      if (control) begin
        count <= count + 1;
      end else begin
        count <= count - 1;
      end
    end
  end

endmodule
