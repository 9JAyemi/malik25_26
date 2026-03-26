module counter_3bit (
  input clk,
  input reset,
  input load,
  input [2:0] input_value,
  output reg [2:0] count
);

  always @ (posedge clk or negedge reset) begin
    if (!reset) begin
      count <= 3'b0;
    end else if (load) begin
      count <= input_value;
    end else if (count == 3'b111) begin
      count <= 3'b0;
    end else begin
      count <= count + 1;
    end
  end

endmodule
