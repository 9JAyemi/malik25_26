// SVA for vga_linear
// Bind module: concise but covers all key functionality and timing

module vga_linear_sva (
  input  logic         clk,
  input  logic         rst,

  // DUT ports
  input  logic [17:1]  csr_adr_o,
  input  logic [15:0]  csr_dat_i,
  input  logic         csr_stb_o,

  input  logic [9:0]   h_count,
  input  logic [9:0]   v_count,
  input  logic         horiz_sync_i,
  input  logic         video_on_h_i,
  input  logic         video_on_h_o,

  input  logic [7:0]   color,
  input  logic         horiz_sync_o,

  // DUT internals
  input  logic [9:0]   row_addr,
  input  logic [6:0]   col_addr,
  input  logic [14:1]  word_offset,
  input  logic [1:0]   plane_addr,
  input  logic [1:0]   plane_addr0,
  input  logic [7:0]   color_l,
  input  logic [4:0]   video_on_h,
  input  logic [4:0]   horiz_sync,
  input  logic [5:0]   pipe
);

  default clocking cb @(posedge clk); endclocking

  // Reset behavior
  assert property (@cb rst |-> (pipe==6'b0));
  assert property (@cb rst |-> (video_on_h==5'b0 && horiz_sync==5'b0));
  assert property (@cb rst |-> (row_addr==10'h0 && col_addr==7'h0 &&
                                plane_addr0==2'b00 && word_offset==14'h0 && plane_addr==2'b00));
  assert property (@cb rst |-> (color_l==8'h00));

  // Shift registers
  assert property (@cb disable iff (rst) pipe == { $past(pipe[4:0]), ~h_count[0] });
  assert property (@cb disable iff (rst) video_on_h == { $past(video_on_h[3:0]), video_on_h_i });
  assert property (@cb disable iff (rst) horiz_sync == { $past(horiz_sync[3:0]), horiz_sync_i });

  // Output taps/delays
  assert property (@cb video_on_h_o == video_on_h[4]);
  assert property (@cb horiz_sync_o == horiz_sync[4]);
  assert property (@cb disable iff (rst) video_on_h_o == $past(video_on_h_i,4));
  assert property (@cb disable iff (rst) horiz_sync_o == $past(horiz_sync_i,4));

  // Address generation equality and stability at strobe
  assert property (@cb csr_adr_o == {word_offset, plane_addr, 1'b0});
  assert property (@cb csr_stb_o == pipe[1]);
  assert property (@cb csr_stb_o |-> $stable(csr_adr_o));

  // Row/col/plane computation
  assert property (@cb disable iff (rst) row_addr == ({v_count[8:1],2'b00} + v_count[8:1]));
  assert property (@cb disable iff (rst) col_addr == h_count[9:3]);
  assert property (@cb disable iff (rst) plane_addr0 == h_count[2:1]);
  assert property (@cb disable iff (rst) plane_addr == $past(plane_addr0));
  assert property (@cb disable iff (rst)
                   word_offset == { $past(row_addr) + $past(col_addr[6:4]), $past(col_addr[3:0]) });

  // Pipe bit propagation sanity (concise form for key taps)
  assert property (@cb disable iff (rst) pipe[1] == $past(pipe[0]));
  assert property (@cb disable iff (rst) pipe[2] == $past(pipe[1]));
  assert property (@cb disable iff (rst) pipe[3] == $past(pipe[2]));
  assert property (@cb disable iff (rst) pipe[4] == $past(pipe[3]));
  assert property (@cb disable iff (rst) pipe[5] == $past(pipe[4]));

  // Color datapath: mux and latch behavior
  assert property (@cb (pipe[4])  |-> (color == csr_dat_i[7:0]));
  assert property (@cb (!pipe[4]) |-> (color == color_l));
  assert property (@cb disable iff (rst) color_l == (pipe[4] ? csr_dat_i[7:0] : $past(color_l)));

  // Functional covers (minimal but meaningful)
  cover property (@cb disable iff (rst) pipe[1]);
  cover property (@cb disable iff (rst) pipe[4]);                          // data phase
  cover property (@cb disable iff (rst) csr_stb_o ##3 pipe[4]);            // strobe -> data
  cover property (@cb disable iff (rst) $rose(video_on_h_o));
  cover property (@cb disable iff (rst) $fell(video_on_h_o));
  cover property (@cb disable iff (rst) $rose(horiz_sync_o));
  cover property (@cb disable iff (rst) (plane_addr==2'b00) ##1 (plane_addr==2'b01)
                                    ##1 (plane_addr==2'b10) ##1 (plane_addr==2'b11));
  cover property (@cb disable iff (rst) word_offset != $past(word_offset));

endmodule

// Bind this SVA to the DUT (example)
// bind vga_linear vga_linear_sva u_vga_linear_sva (
//   .clk(clk), .rst(rst),
//   .csr_adr_o(csr_adr_o), .csr_dat_i(csr_dat_i), .csr_stb_o(csr_stb_o),
//   .h_count(h_count), .v_count(v_count), .horiz_sync_i(horiz_sync_i), .video_on_h_i(video_on_h_i),
//   .video_on_h_o(video_on_h_o), .color(color), .horiz_sync_o(horiz_sync_o),
//   .row_addr(row_addr), .col_addr(col_addr), .word_offset(word_offset),
//   .plane_addr(plane_addr), .plane_addr0(plane_addr0), .color_l(color_l),
//   .video_on_h(video_on_h), .horiz_sync(horiz_sync), .pipe(pipe)
// );