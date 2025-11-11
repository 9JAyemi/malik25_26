
module vga_converter (
  input [23:0] data,
  input blank,
  input hs,
  input vs,
  input clk,
  output [7:0] vga_data,
  output blank_out,
  output hs_out,
  output vs_out
);

  reg [1:0] cnt;
  reg [23:0] data_reg;
  reg hs_reg;
  reg hs_reg1;
  reg vs_reg;
  reg blank_reg;

  always @(posedge clk) begin
    hs_reg <= hs;
    hs_reg1 <= hs_reg;
    vs_reg <= vs;
    blank_reg <= blank;
  end

  wire sync_pulse = (hs_reg & !hs_reg1) ? 1'b1 : 1'b0;
  always @(posedge clk) begin
    if (sync_pulse) begin
      cnt <= 2'b11; 
    end
    else begin
      if (cnt == 2)
        cnt <= 2'b00;
      else    
        cnt <= cnt+1;
    end
  end

  always @(posedge clk) begin
    if (cnt == 2'b11)
      data_reg <= data;
  end

  assign vga_data = {3'b0, cnt[1] ? data_reg[23:16] : (cnt[0] ? data_reg[15:8] : data_reg[7:0])};
  assign blank_out = blank_reg & cnt != 0;
  assign hs_out = hs_reg & cnt != 0;
  assign vs_out = vs_reg & cnt != 0;

endmodule