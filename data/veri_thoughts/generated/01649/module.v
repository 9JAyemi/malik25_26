
module CLK_GEN(
  input CLK_IN,
  output reg CLK_OUT
);

reg [24:0] counter;

always @(posedge CLK_IN) begin
  counter <= counter + 1;
  if (counter == 25'd4166) begin
    counter <= 0;
    CLK_OUT <= ~CLK_OUT;
  end
end

endmodule