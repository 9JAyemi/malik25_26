module sync_counter(
  input clk,
  input reset_n,
  input enable,
  output reg [3:0] count
);

  always @(posedge clk or negedge reset_n) begin
    if (~reset_n) begin
      count <= 4'b0;
    end
    else if (enable) begin
      count <= count + 1;
    end
  end

endmodule