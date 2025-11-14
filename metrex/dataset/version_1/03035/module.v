
module toggle_module (
   input clk,
   input toggle,
   input [7:0] cyc_copy,
   output reg toggle_up
);

   reg [7:0] cyc_count;
   reg [7:0] cyc_copy_reg;

   always @(posedge clk) begin
      if (toggle) begin
         cyc_count <= 0;
         cyc_copy_reg <= cyc_copy;
      end else begin
         if (cyc_count == cyc_copy_reg) begin
            toggle_up <= ~toggle_up;
            cyc_count <= 0;
         end else begin
            cyc_count <= cyc_count + 1;
            cyc_copy_reg <= cyc_copy;
         end
      end
   end

endmodule