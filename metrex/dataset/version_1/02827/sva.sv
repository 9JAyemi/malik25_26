// SVA for vga_double. Bind this file; focus on key control/data invariants and compact coverage.

module vga_double_asserts;

  default clocking cb @(posedge clk); endclocking

  // Basic protocol: starts are single-cycle pulses
  assert property (!(hsync_start && $past(hsync_start)));
  assert property (hsync_start |=> !hsync_start);

  assert property (!(scanin_start && $past(scanin_start)));
  assert property (scanin_start |=> !scanin_start);

  assert property (!(scanout_start && $past(scanout_start)));
  assert property (scanout_start |=> !scanout_start);

  // Page flip behavior
  assert property (hsync_start |=> pages == ~$past(pages));
  assert property (!hsync_start |=> pages == $past(pages));

  // Address mapping to memory instance and page separation
  assert property (line_buf.wraddr == {ptr_in[9:8],  pages,    ptr_in[7:0]});
  assert property (line_buf.rdaddr == {ptr_out[9:8], ~pages,   ptr_out[7:0]});
  assert property (line_buf.wraddr[8] == pages && line_buf.rdaddr[8] == ~pages);
  assert property (!(wr_stb && (line_buf.wraddr == line_buf.rdaddr)));

  // Address range while active (never use ptr[9:8]==2'b11 for access)
  assert property ((ptr_in[9:8]  != 2'b11) |-> line_buf.wraddr <= 11'd1535);
  assert property ((ptr_out[9:8] != 2'b11) |-> line_buf.rdaddr <= 11'd1535);

  // ptr_in control: reset fields, toggle wr_stb when active, increment on write only
  assert property (scanin_start |=> (ptr_in[9:8]==2'b00 && ptr_in[5:4]==2'b11));
  assert property ((ptr_in[9:8]!=2'b11 && !$past(scanin_start)) |-> wr_stb != $past(wr_stb));
  assert property (($past(ptr_in[9:8]!=2'b11) && $past(!scanin_start) && $past(wr_stb)) |=> ptr_in == $past(ptr_in)+10'd1);
  assert property (($past(ptr_in[9:8]!=2'b11) && $past(!scanin_start) && !$past(wr_stb)) |=> ptr_in == $past(ptr_in));
  assert property (ptr_in[9:8]==2'b11 |-> wr_stb==1'b0);

  // ptr_out control: reset fields, increment every cycle while active
  assert property (scanout_start |=> (ptr_out[9:8]==2'b00 && ptr_out[5:4]==2'b11));
  assert property ((ptr_out[9:8]!=2'b11 && !scanout_start) |=> ptr_out == $past(ptr_out)+10'd1);
  assert property ((ptr_out[9:8]==2'b11 && !scanout_start) |=> ptr_out == $past(ptr_out));

  // Pixel output muxing
  assert property ((ptr_out[9:8]!=2'b11) |=> pix_out == $past(data_out[5:0]));
  assert property ((ptr_out[9:8]==2'b11) |=> pix_out == 6'd0);

  // Functional coverage
  cover property (scanin_start  ##[1:900]  ptr_in[9:8]==2'b11);
  cover property (scanout_start ##[1:900]  ptr_out[9:8]==2'b11);
  cover property (pages==1'b0 ##1 hsync_start ##1 pages==1'b1);  // page flip observed
  cover property (ptr_in[9:8]==2'b00 ##[1:2000] ptr_in[9:8]==2'b01 ##[1:2000] ptr_in[9:8]==2'b10); // three segments used
  cover property (ptr_out[9:8]==2'b00 ##[1:2000] ptr_out[9:8]==2'b01 ##[1:2000] ptr_out[9:8]==2'b10);

endmodule

bind vga_double vga_double_asserts vga_double_asserts_i();