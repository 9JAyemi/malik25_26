

module altera_tse_false_path_marker 
#(
   parameter MARKER_WIDTH = 1
)
(
   input    reset,
   input    clk,
   input    [MARKER_WIDTH - 1 : 0] data_in,
   output   [MARKER_WIDTH - 1 : 0] data_out
);



 reg [MARKER_WIDTH - 1 : 0] data_out_reg;


assign data_out = data_out_reg;

always @(posedge clk or posedge reset) 
begin
   if (reset)
   begin
      data_out_reg <= {MARKER_WIDTH{1'b0}};
   end
   else
   begin
      data_out_reg <= data_in;
   end
end

endmodule
