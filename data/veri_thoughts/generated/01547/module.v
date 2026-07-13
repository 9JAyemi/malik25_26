
module RegisterMultiplexer(clk, rst, load, D, Q);
  input clk, rst, load;
  input [11:0] D;
  output [11:0] Q;
  reg [11:0] Q;

  always @(posedge clk or posedge rst) begin
    if (rst) begin
      Q <= 12'b0;
    end else if (load) begin
      Q <= D;
    end
  end

endmodule
