module timer #(
    parameter res   = 33,   parameter phase = 12507 )
  (
    input      wb_clk_i,	  	input      wb_rst_i,
    output reg wb_tgc_o   		);

  reg [res-1:0] cnt;
  reg           old_clk2;
  wire          clk2;

  assign clk2 = cnt[res-1];

  always @(posedge wb_clk_i)
    cnt <= wb_rst_i ? 0 : (cnt + phase);

  always @(posedge wb_clk_i)
    old_clk2 <= wb_rst_i ? 1'b0 : clk2;

  always @(posedge wb_clk_i)
    wb_tgc_o <= wb_rst_i ? 1'b0 : (!old_clk2 & clk2);

endmodule
