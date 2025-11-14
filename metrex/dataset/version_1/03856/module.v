
module pipeline_module( input in, input clk, output out );
  wire inv_in;
  reg inv_out;

  assign inv_in = ~in;
  assign out = inv_out;

  always @(posedge clk) begin
    inv_out <= inv_in;
  end
endmodule
