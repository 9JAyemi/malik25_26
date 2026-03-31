
module posManager (
   input         clk,
   input [15:0]  pos11,
   input [15:0]  pos12,
   input [15:0]  pos21,
   input [15:0]  pos22,
   output [15:0] pos_diff_x,
   output [15:0] pos_diff_y,
   output [31:0] count_clk,
   input  [1:0]  clear,
   input  [0:0]  m1,
   input  [0:0]  m2
);

   reg [15:0] prev_pos11, prev_pos12, prev_pos21, prev_pos22;
   reg [31:0] prev_count_clk;

   always @(posedge clk) begin
      if (clear == 2'b10 || clear == 2'b11) begin
         prev_count_clk <= 0;
      end else begin
         prev_count_clk <= prev_count_clk + 1;
      end

      if (clear == 2'b01 || clear == 2'b10 || clear == 2'b11) begin
         prev_pos11 <= pos11;
         prev_pos12 <= pos12;
         prev_pos21 <= pos21;
         prev_pos22 <= pos22;
      end else begin
         if (m1 == 1'b1) begin
            prev_pos11 <= prev_pos11 + 1;
            prev_pos12 <= prev_pos12 + 1;
         end else begin
            prev_pos11 <= prev_pos11 - 1;
            prev_pos12 <= prev_pos12 - 1;
         end

         if (m2 == 1'b1) begin
            prev_pos21 <= prev_pos21 + 1;
            prev_pos22 <= prev_pos22 + 1;
         end else begin
            prev_pos21 <= prev_pos21 - 1;
            prev_pos22 <= prev_pos22 - 1;
         end
      end
   end

   assign pos_diff_x = clear == 2'b10 || clear == 2'b11 ? 0 : pos11 - pos21;
   assign pos_diff_y = clear == 2'b10 || clear == 2'b11 ? 0 : pos12 - pos22;
   assign count_clk = clear == 2'b10 || clear == 2'b11 ? 0 : prev_count_clk;

endmodule
