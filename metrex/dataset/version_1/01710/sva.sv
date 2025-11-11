// SystemVerilog Assertions for rgb_generator
// Place inside the module (e.g., near the end) or wrap with `ifdef SVA.
// These assertions focus on correctness and concise full-coverage of key behavior.

`ifndef RGB_GENERATOR_SVA
`define RGB_GENERATOR_SVA

// synthesis translate_off
default clocking cb @(posedge clk); endclocking
default disable iff (rst)

// Reset/state basics
assert property (rst |=> state == IDLE);
assert property (o_vblank == (state == VID));

// Clock divider/start pulse
assert property (r_clk_div_count <= VBLANK_TIMEOUT);
assert property ((r_clk_div_count < VBLANK_TIMEOUT) |=> (r_clk_div_count == $past(r_clk_div_count)+1) && !r_start_stb);
assert property ((r_clk_div_count == VBLANK_TIMEOUT) |=> (r_clk_div_count == 0) && r_start_stb);
assert property (r_start_stb |=> !r_start_stb);

// IDLE -> VID entry and init
assert property ((state == IDLE && r_start_stb) |=> (state == VID && r_x_pos == 0 && r_y_pos == 0 && r_nes_x_next == 1));

// VID scan progression
assert property ((state == VID && (r_y_pos < (FRAME_HEIGHT+VBLANK)) && (r_x_pos < (FRAME_WIDTH+HBLANK)))
                 |=> r_x_pos == $past(r_x_pos)+1);
assert property ((state == VID && (r_y_pos < (FRAME_HEIGHT+VBLANK)) && (r_x_pos == (FRAME_WIDTH+HBLANK)))
                 |=> (r_x_pos == 0) && (r_y_pos == $past(r_y_pos)+1));
assert property ((state == VID && (r_y_pos >= (FRAME_HEIGHT+VBLANK))) |=> state == IDLE);

// Range sanity
assert property (r_x_pos <= FRAME_WIDTH + HBLANK);
assert property (r_y_pos <= FRAME_HEIGHT + VBLANK);

// SOF strobe (one cycle at x=0,y=0)
assert property (o_sof_stb |-> (state == VID && r_x_pos == 0 && r_y_pos == 0));
assert property ((state == VID && r_x_pos == 0 && r_y_pos == 0) |-> o_sof_stb);
assert property (o_sof_stb |=> !o_sof_stb);

// HSync protocol per line
assert property ((state == VID && r_x_pos < FRAME_WIDTH) |-> o_video_hsync);
assert property ((state == VID && r_x_pos >= FRAME_WIDTH) |-> !o_video_hsync);

// Valid pipeline
assert property (r_valid == $past(w_valid));

// Background/color muxing
assert property (w_bg_color == BG_COLOR);
assert property (!r_valid |-> (r_rgb == 8'h00) &&
                 (o_r_out == w_bg_color[7:5]) && (o_g_out == w_bg_color[4:2]) && (o_b_out == w_bg_color[1:0]));
assert property ( r_valid |-> (o_r_out == r_rgb[7:5]) && (o_g_out == r_rgb[4:2]) && (o_b_out == r_rgb[1:0]));

// NES coordinate mapping
assert property ( w_valid |-> (w_x_pos == r_x_pos - X_OFFSET) && (w_y_pos == r_y_pos - Y_OFFSET));
assert property (!w_valid |-> (w_x_pos == 0) && (w_y_pos == 0));
assert property ((o_nes_x_out[9] == 1'b0) && (o_nes_x_out[8:0] == w_x_pos));
assert property ((o_nes_y_out[9] == 1'b0) && (o_nes_y_out[8:0] == w_y_pos));
assert property ( w_valid |-> (o_nes_y_next_out == o_nes_y_out + 10'd1));
assert property (!w_valid |-> (o_nes_y_next_out == 10'd1));

// Pixel pulse region and exclusivity
assert property (! (state == VID) |-> !o_pix_pulse_out);
assert property (o_pix_pulse_out |-> (state == VID) &&
                 (r_x_pos < FRAME_WIDTH) &&
                 (r_y_pos >= (Y_OFFSET - 1)) && (r_y_pos < (Y_OFFSET + IMAGE_HEIGHT)) &&
                 (r_x_pos >= (X_OFFSET - 1)) && (r_x_pos < (X_OFFSET + IMAGE_WIDTH)));
assert property ((state == VID) &&
                 (r_x_pos < FRAME_WIDTH) &&
                 (r_y_pos >= (Y_OFFSET - 1)) && (r_y_pos < (Y_OFFSET + IMAGE_HEIGHT)) &&
                 (r_x_pos >= (X_OFFSET - 1)) && (r_x_pos < (X_OFFSET + IMAGE_WIDTH))
                 |-> o_pix_pulse_out);

// Coverage
cover property (r_start_stb);
cover property (state == VID && r_x_pos == 0 && r_y_pos == 0);                       // SOF
cover property (state == VID && r_x_pos == FRAME_WIDTH+HBLANK ##1 r_x_pos == 0);     // EOL wrap
cover property (state == VID && r_y_pos == FRAME_HEIGHT+VBLANK ##1 state == IDLE);   // EOF to IDLE
cover property (state == VID && r_y_pos == Y_OFFSET && r_x_pos == X_OFFSET && w_valid);
cover property (state == VID && r_y_pos == (Y_OFFSET+IMAGE_HEIGHT-1) &&
                r_x_pos == (X_OFFSET+IMAGE_WIDTH-1) && w_valid);
cover property (o_pix_pulse_out);

// synthesis translate_on
`endif