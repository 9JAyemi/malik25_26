module memory_to_color(
  input  [1:0]  color_depth_i,
  input  [31:0] mem_i,
  input  [1:0]  mem_lsb_i,
  output [31:0] color_o,
  output [3:0]  sel_o
);

  assign sel_o = (color_depth_i == 2'b00) ? // 8-bit
                  (mem_lsb_i == 2'b00) ? 4'b0001 : // least significant byte
                  (mem_lsb_i == 2'b01) ? 4'b0010 : // second least significant byte
                  (mem_lsb_i == 2'b10) ? 4'b0100 : // third least significant byte
                  (mem_lsb_i == 2'b11) ? 4'b1000 : // most significant byte
                  4'bxxxx : // error
                (color_depth_i == 2'b01) ? // 16-bit
                  (mem_lsb_i == 2'b0) ? 4'b0011 : // low word
                  (mem_lsb_i == 2'b1) ? 4'b1100 : // high word
                  4'bxxxx : // error
                (color_depth_i == 2'b10) ? 4'b1111 : // 32-bit
                  4'bxxxx; // error

  assign color_o = (color_depth_i == 2'b00) ? // 8-bit
                  (mem_lsb_i == 2'b00) ? {mem_i[31:24], 8'h00, 8'h00} : // least significant byte
                  (mem_lsb_i == 2'b01) ? {8'h00, mem_i[23:16], 8'h00} : // second least significant byte
                  (mem_lsb_i == 2'b10) ? {8'h00, 8'h00, mem_i[15:8]} : // third least significant byte
                  (mem_lsb_i == 2'b11) ? {8'h00, 8'h00, 8'h00, mem_i[7:0]} : // most significant byte
                  32'hxxxxxxxx : // error
                (color_depth_i == 2'b01) ? // 16-bit
                  (mem_lsb_i == 2'b0) ? {mem_i[31:16], 16'h0000} : // low word
                  (mem_lsb_i == 2'b1) ? {16'h0000, mem_i[15:0]} : // high word
                  32'hxxxxxxxx : // error
                (color_depth_i == 2'b10) ? // 32-bit
                  mem_i : // use entire memory data
                  32'hxxxxxxxx; // error

endmodule