module up_down_counter (
  input clk,
  input areset,
  input up_down,
  input load,
  input [3:0] load_value,
  output reg [3:0] count
);

  always @(posedge clk or negedge areset) begin
    if (areset == 0) begin
      count <= 0;
    end else if (load == 1) begin
      count <= load_value;
    end else if (up_down == 1) begin
      count <= count + 1;
    end else begin
      count <= count - 1;
    end
  end
  
endmodule
