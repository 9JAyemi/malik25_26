
module match (
   input  [15:0] vec_i,
   input         b8_i,
   input         b12_i,
   output reg        match1_o,
   output reg        match2_o
   );

   always @* begin
      match1_o = (vec_i[15:14] == 2'b00) &&
                   (vec_i[11] == 1'b0) &&
                   (vec_i[7] == b8_i) &&
                   (vec_i[3] == b12_i);

      match2_o = (vec_i[15:14] == 2'b00) &&
                   (vec_i[7] == b8_i) &&
                   (vec_i[3] == b12_i) &&
                   (vec_i[11] == 1'b0);
   end

endmodule
