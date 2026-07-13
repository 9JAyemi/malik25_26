module binary_up_down_counter (
  input clk,
  input reset,
  input up_down,
  input clear,
  input load,
  input [3:0] data_in,
  output reg [3:0] count
);

  always @(posedge clk or posedge reset) begin
    if (reset) begin
      count <= 4'b0;
    end else if (clear) begin
      count <= 4'b0;
    end else if (load) begin
      count <= data_in;
    end else if (up_down) begin
      count <= count + 1;
    end else begin
      count <= count - 1;
    end
  end
  
endmodule
