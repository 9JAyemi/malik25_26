// SVA checker for vga_linear_fml
module vga_linear_fml_sva
(
  input  logic        clk,
  input  logic        rst,
  input  logic        enable,

  // DUT ports
  input  logic [17:1] fml_adr_o,
  input  logic [15:0] fml_dat_i,
  input  logic        fml_stb_o,

  input  logic [9:0]  h_count,
  input  logic [9:0]  v_count,
  input  logic        horiz_sync_i,
  input  logic        video_on_h_i,
  input  logic        video_on_h_o,
  input  logic [7:0]  color,
  input  logic        horiz_sync_o,

  // DUT internals
  input  logic [9:0]  row_addr,
  input  logic [6:0]  col_addr,
  input  logic [14:1] word_offset,
  input  logic [1:0]  plane_addr,
  input  logic [1:0]  plane_addr0,
  input  logic [7:0]  color_l,

  input  logic [15:0] fml1_dat,
  input  logic [15:0] fml2_dat,
  input  logic [15:0] fml3_dat,
  input  logic [15:0] fml4_dat,
  input  logic [15:0] fml5_dat,
  input  logic [15:0] fml6_dat,
  input  logic [15:0] fml7_dat,

  input  logic [4:0]  video_on_h,
  input  logic [4:0]  horiz_sync,
  input  logic [18:0] pipe
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Reset values
  assert property (rst |=> pipe==19'b0);
  assert property (rst |=> video_on_h==5'b0 && horiz_sync==5'b0);
  assert property (rst |=> row_addr==10'h0 && col_addr==7'h0 &&
                          plane_addr0==2'b00 && word_offset==14'h0 &&
                          plane_addr==2'b00 && color_l==8'h00);

  // Hold when not enabled
  assert property (!enable |=> $stable({pipe,video_on_h,horiz_sync,
                                        row_addr,col_addr,plane_addr0,
                                        word_offset,plane_addr,color_l,
                                        fml1_dat,fml2_dat,fml3_dat,fml4_dat,
                                        fml5_dat,fml6_dat,fml7_dat})));

  // Pipe shift and strobe
  assert property (enable |=> pipe == { $past(pipe[17:0]), $past(h_count[3:0]==4'h0) });
  assert property (fml_stb_o == pipe[1]);

  // Shifts for sync/video, and their outputs
  assert property (enable |=> video_on_h == { $past(video_on_h[3:0]), $past(video_on_h_i) });
  assert property (enable |=> horiz_sync == { $past(horiz_sync[3:0]), $past(horiz_sync_i) });
  assert property (video_on_h_o == video_on_h[4]);
  assert property (horiz_sync_o == horiz_sync[4]);

  // Address stage timing
  assert property (enable |=> plane_addr0 == $past(h_count[2:1]));
  assert property (enable |=> col_addr    == $past(h_count[9:3]));
  assert property (enable |=> row_addr    == ({$past(v_count[8:1]),2'b00} + $past(v_count[8:1])));
  // Word offset uses prior row/col; account for truncation of MSB of sum
  assert property (enable |=> word_offset == { ($past(row_addr + col_addr[6:4]))[9:0], $past(col_addr[3:0]) });

  // Address bus mapping
  assert property (fml_adr_o == {1'b0, word_offset, plane_addr});
  assert property (fml_adr_o[17] == 1'b0);

  // Frame-buffer data capture into holding regs
  assert property (enable && pipe[5]  |=> fml1_dat == $past(fml_dat_i));
  assert property (enable && pipe[6]  |=> fml2_dat == $past(fml_dat_i));
  assert property (enable && pipe[7]  |=> fml3_dat == $past(fml_dat_i));
  assert property (enable && pipe[8]  |=> fml4_dat == $past(fml_dat_i));
  assert property (enable && pipe[9]  |=> fml5_dat == $past(fml_dat_i));
  assert property (enable && pipe[10] |=> fml6_dat == $past(fml_dat_i));
  assert property (enable && pipe[11] |=> fml7_dat == $past(fml_dat_i));

  // Color mux on pipe[4]
  assert property (color == (pipe[4] ? fml_dat_i[7:0] : color_l));

  // color_l update priority chain
  assert property (enable && pipe[4]                                   |=> color_l == $past(fml_dat_i[7:0]));
  assert property (enable && !pipe[4] && pipe[5]                       |=> color_l == $past(fml_dat_i[7:0]));
  assert property (enable && !pipe[4] && !pipe[5] && pipe[7]           |=> color_l == $past(fml2_dat[7:0]));
  assert property (enable && !pipe[4] && !pipe[5] && !pipe[7] && pipe[9]   |=> color_l == $past(fml3_dat[7:0]));
  assert property (enable && !pipe[4] && !pipe[5] && !pipe[7] && !pipe[9] && pipe[11] |=> color_l == $past(fml4_dat[7:0]));
  assert property (enable && !(pipe[4]|pipe[5]|pipe[7]|pipe[9]|pipe[11]) && pipe[13]  |=> color_l == $past(fml5_dat[7:0]));
  assert property (enable && !(pipe[4]|pipe[5]|pipe[7]|pipe[9]|pipe[11]|pipe[13]) && pipe[15] |=> color_l == $past(fml6_dat[7:0]));
  assert property (enable && !(pipe[4]|pipe[5]|pipe[7]|pipe[9]|pipe[11]|pipe[13]|pipe[15]) && pipe[17] |=> color_l == $past(fml7_dat[7:0]));

  // Key covers
  cover property (enable ##1 pipe[0]);                       // pipeline inject
  cover property (pipe[1]);                                  // strobe phase
  cover property (pipe[4] && (color==fml_dat_i[7:0]));       // direct color path
  cover property (enable && pipe[5]);                        // capture into fml1_dat
  cover property (enable && pipe[11]);                       // capture into fml7_dat
  cover property (enable && pipe[7]);                        // later color_l sourcing
  cover property (video_on_h_o);                             // video_on shift seen
  cover property (horiz_sync_o);                             // hsync shift seen

endmodule

// Bind into DUT (auto-connects by name, including internals listed above)
bind vga_linear_fml vga_linear_fml_sva sva_i (.*);