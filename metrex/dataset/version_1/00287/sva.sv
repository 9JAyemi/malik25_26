// SVA for DrawMarioScore
module DrawMarioScore_sva #(
  parameter int XPOS   = 40,
  parameter int YPOS   = 50,
  parameter int WIDTH  = 552,
  parameter int HEIGHT = 16
)(
  input  logic        clk,
  input  logic        rst,
  input  logic [9:0]  hcount_in,
  input  logic        hsync_in,
  input  logic [9:0]  vcount_in,
  input  logic        vsync_in,
  input  logic [23:0] rgb_in,
  input  logic        blnk_in,
  input  logic [7:0]  char_pixels,

  input  logic [9:0]  hcount_out,
  input  logic        hsync_out,
  input  logic [9:0]  vcount_out,
  input  logic        vsync_out,
  input  logic [23:0] rgb_out,
  input  logic        blnk_out,
  input  logic [7:0]  char_xy,
  input  logic [3:0]  char_line
);

  logic past_valid;
  always_ff @(posedge clk or posedge rst) begin
    if (rst) past_valid <= 1'b0;
    else     past_valid <= 1'b1;
  end

  default clocking cb @(posedge clk); endclocking
  default disable iff (!past_valid);

  // Common window predicate
  let inside_win = (hcount_in >= XPOS) && (hcount_in < XPOS+WIDTH) &&
                   (vcount_in >= YPOS) && (vcount_in < YPOS+HEIGHT);

  // Asynchronous reset drives zeros immediately and held during rst
  assert property (@(posedge rst)
    (hcount_out==0 && vcount_out==0 && hsync_out==0 && vsync_out==0 && rgb_out==0 && blnk_out==0)
  );
  assert property (@(posedge clk)
    rst |-> (hcount_out==0 && vcount_out==0 && hsync_out==0 && vsync_out==0 && rgb_out==0 && blnk_out==0)
  );

  // Registered pass-through behavior (1-cycle latency due to NBA sampling)
  assert property (
    !rst |-> (hcount_out==$past(hcount_in) &&
              vcount_out==$past(vcount_in) &&
              hsync_out==$past(hsync_in) &&
              vsync_out==$past(vsync_in) &&
              blnk_out==$past(blnk_in))
  );

  // Combinational outputs char_xy / char_line functions
  assert property (char_xy   == (((hcount_in - XPOS - 1) >> 3) & 8'hFF));
  assert property (char_line == ((vcount_in - YPOS) & 4'hF));

  // When drawing a pixel (per RTL condition), rgb_out is white or yellow based on char_xy
  assert property (
    $past( inside_win && (char_pixels[(XPOS - hcount_in)] === 1'b1) )
      |-> rgb_out == ( ($past(char_xy)==8'h20) ? 24'hFF_FF_00 : 24'hFF_FF_FF )
  );

  // Otherwise, rgb_out passes through rgb_in
  assert property (
    $past( !(inside_win && (char_pixels[(XPOS - hcount_in)] === 1'b1)) )
      |-> (rgb_out == $past(rgb_in))
  );

  // Sanity: within vertical window, char_line must be in range
  assert property (
    ((vcount_in >= YPOS) && (vcount_in < YPOS+HEIGHT)) |-> ($unsigned(char_line) < HEIGHT)
  );

  // Bounds check on dynamic bit select into char_pixels (flags likely bug in RTL)
  assert property (
    inside_win |-> ($unsigned(XPOS - hcount_in) < 8)
  );

  // Coverage: exercise draw paths (yellow and white) and pass-through path
  cover property (
    $past( inside_win && (char_pixels[(XPOS - hcount_in)] === 1'b1) ) &&
    ($past(char_xy)==8'h20) && (rgb_out==24'hFF_FF_00)
  );
  cover property (
    $past( inside_win && (char_pixels[(XPOS - hcount_in)] === 1'b1) ) &&
    ($past(char_xy)!=8'h20) && (rgb_out==24'hFF_FF_FF)
  );
  cover property (
    $past(!inside_win) && (rgb_out==$past(rgb_in))
  );

endmodule

// Bind into DUT
bind DrawMarioScore DrawMarioScore_sva #(
  .XPOS(40), .YPOS(50), .WIDTH(552), .HEIGHT(16)
) u_DrawMarioScore_sva (
  .clk(clk), .rst(rst),
  .hcount_in(hcount_in), .hsync_in(hsync_in), .vcount_in(vcount_in), .vsync_in(vsync_in),
  .rgb_in(rgb_in), .blnk_in(blnk_in), .char_pixels(char_pixels),
  .hcount_out(hcount_out), .hsync_out(hsync_out), .vcount_out(vcount_out), .vsync_out(vsync_out),
  .rgb_out(rgb_out), .blnk_out(blnk_out), .char_xy(char_xy), .char_line(char_line)
);