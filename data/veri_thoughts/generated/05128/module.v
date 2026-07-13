
module binary_counter (
   input clk,
   input reset,
   input enable,
   output reg [2:0] count
);

   reg [2:0] shift_reg;
   reg [1:0] flip_flop;

   always @(posedge clk) begin
      if (reset) begin
         shift_reg <= 3'b0;
         flip_flop <= 2'b0;
         count <= 3'b0;
      end else if (enable) begin
         flip_flop <= {flip_flop[0], shift_reg[2]};
         shift_reg <= {flip_flop[1], shift_reg[2:1]};
         count <= shift_reg;
      end
   end

endmodule