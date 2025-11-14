module video_timing_gen (
  input aclk, rst,
  input axis_tready, axis_tvalid,
  input [23:0] axis_video,
  input axis_eol, axis_sof,
  input [1:0] fid,
  input [11:0] active_pixels,
  input [11:0] active_lines,
  output reg video_clk, ce,
  output [11:0] total_lines,
  output [11:0] vsync_start, vsync_end,
  output [11:0] total_pixels,
  output [11:0] hsync_start, hsync_end,
  output reg vtg_hsync, vtg_vsync, vtg_vblank, vtg_hblank, vtg_act_vid,
  output reg [1:0] vtg_field_id
);

  // Constants
  parameter H_SYNC_WIDTH = 96;
  parameter H_BLANK_WIDTH = 208;
  parameter V_SYNC_WIDTH = 2;
  parameter V_BLANK_WIDTH = 35;

  // Internal signals
  reg [11:0] line_count = 0;
  reg [11:0] pixel_count = 0;
  reg [11:0] vsync_start_time = 0;
  reg [11:0] vsync_end_time = 0;
  reg [11:0] hsync_start_time = 0;
  reg [11:0] hsync_end_time = 0;
  reg [11:0] total_pixels_reg = 0;
  reg [11:0] total_lines_reg = 0;
  reg [1:0] field_id_reg = 0;

  // Video data input
  reg [7:0] r, g, b;

  always @(posedge aclk) begin
    if (rst) begin
      video_clk <= 0;
      ce <= 0;
      line_count <= 0;
      pixel_count <= 0;
      vsync_start_time <= 0;
      vsync_end_time <= 0;
      hsync_start_time <= 0;
      hsync_end_time <= 0;
      total_pixels_reg <= 0;
      total_lines_reg <= 0;
      field_id_reg <= 0;
      vtg_hsync <= 0;
      vtg_vsync <= 0;
      vtg_vblank <= 0;
      vtg_hblank <= 0;
      vtg_act_vid <= 0;
      vtg_field_id <= 0;
    end else begin
      // Video timing generator
      if (line_count < active_lines) begin
        vtg_act_vid <= 1;
      end else begin
        vtg_act_vid <= 0;
      end
      if (line_count < active_lines + V_SYNC_WIDTH) begin
        vtg_vsync <= 0;
      end else if (line_count < active_lines + V_SYNC_WIDTH + V_BLANK_WIDTH) begin
        vtg_vsync <= 1;
        vtg_vblank <= 1;
      end else if (line_count < 2*active_lines + V_SYNC_WIDTH + V_BLANK_WIDTH) begin
        vtg_vsync <= 0;
        vtg_vblank <= 0;
      end else if (line_count < 2*active_lines + 2*V_SYNC_WIDTH + V_BLANK_WIDTH) begin
        vtg_vsync <= 1;
        vtg_vblank <= 1;
      end else begin
        vtg_vsync <= 0;
        vtg_vblank <= 0;
      end
      if (pixel_count < active_pixels) begin
        vtg_hsync <= 1;
        vtg_hblank <= 0;
        vtg_field_id <= field_id_reg;
      end else if (pixel_count < active_pixels + H_SYNC_WIDTH) begin
        vtg_hsync <= 0;
        vtg_hblank <= 0;
      end else if (pixel_count < active_pixels + H_SYNC_WIDTH + H_BLANK_WIDTH) begin
        vtg_hsync <= 0;
        vtg_hblank <= 1;
      end else begin
        vtg_hsync <= 0;
        vtg_hblank <= 0;
        pixel_count <= 0;
        line_count <= line_count + 1;
        if (line_count >= 2*active_lines + 2*V_SYNC_WIDTH + V_BLANK_WIDTH) begin
          line_count <= 0;
          total_lines_reg <= total_lines_reg + 1;
          field_id_reg <= ~field_id_reg;
        end
      end

      // Video clock generator
      if (pixel_count == active_pixels - 1) begin
        video_clk <= 1;
        total_pixels_reg <= total_pixels_reg + active_pixels;
        pixel_count <= 0;
        ce <= 1;
      end else begin
        video_clk <= 0;
        pixel_count <= pixel_count + 1;
        ce <= 0;
      end

      // Video data input
      if (axis_tvalid && axis_tready) begin
        r <= axis_video[23:16];
        g <= axis_video[15:8];
        b <= axis_video[7:0];
      end

      // Vertical sync pulse timing
      if (line_count == active_lines + V_SYNC_WIDTH) begin
        vsync_start_time <= total_pixels_reg + pixel_count;
      end
      if (line_count == active_lines + V_SYNC_WIDTH + V_BLANK_WIDTH) begin
        vsync_end_time <= total_pixels_reg + pixel_count;
      end

      // Horizontal sync pulse timing
      if (pixel_count == active_pixels + H_SYNC_WIDTH) begin
        hsync_start_time <= total_pixels_reg + pixel_count;
      end
      if (pixel_count == active_pixels + H_SYNC_WIDTH + H_BLANK_WIDTH) begin
        hsync_end_time <= total_pixels_reg + pixel_count;
      end
    end
  end

  assign total_pixels = total_pixels_reg;
  assign total_lines = total_lines_reg;
  assign vsync_start = vsync_start_time;
  assign vsync_end = vsync_end_time;
  assign hsync_start = hsync_start_time;
  assign hsync_end = hsync_end_time;

endmodule