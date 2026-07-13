module toggle_module #(
   parameter WIDTH = 1
)(
   input clk,
   input toggle,
   output reg [WIDTH-1:0] out
);


always @(posedge clk) begin
   if (toggle && !out) begin
      out <= 1;
   end else if (toggle && out) begin
      out <= 0;
   end
end

endmodule