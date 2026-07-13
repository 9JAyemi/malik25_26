
module d_flip_flop_as (
  input wire clk,
  input wire as,
  input [7:0] d,
  output reg [7:0] q
);

  always @(posedge clk) begin
    if(~as) begin
      q <= d;
    end  
  end

endmodule