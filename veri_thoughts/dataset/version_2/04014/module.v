module up_counter (
  input clk,
  input reset,
  input load,
  input [3:0] load_value,
  output reg [3:0] count
);

  always @(posedge clk or negedge reset) begin
    if (reset == 0) begin
      count <= 4'b0000;
    end else if (load == 1) begin
      count <= load_value;
    end else begin
      count <= count + 1;
    end
  end
  
endmodule
