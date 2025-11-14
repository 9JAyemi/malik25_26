// SVA checker for axis_gen_pulse
// Bind this file to the DUT. Focuses on protocol, counters, flags, data mapping, and interlace behavior.

module axis_gen_pulse_sva #(
  parameter int DLY = 1,
  parameter bit INTERLACE = 0,
  parameter int DATA_WIDTH = 24
)(
  input  logic                    aclk,
  input  logic                    rst,
  input  logic                    axis_tready,
  input  logic                    axis_tvalid,
  input  logic [DATA_WIDTH-1:0]   axis_tdata_video,
  input  logic                    axis_tlast,
  input  logic                    fid,
  input  logic                    axis_tuser_sof,
  input  logic                    axis_tuser_pulse,
  input  logic [13:0]             active_pixels,
  input  logic [13:0]             active_lines
);

  // Mirror expected counters based on handshake
  logic [13:0] exp_pixel, exp_line;

  always_ff @(posedge aclk) begin
    if (rst) begin
      exp_pixel <= '0;
      exp_line  <= '0;
    end else if (axis_tready) begin
      if (exp_pixel == active_pixels-1) begin
        exp_pixel <= '0;
        if (exp_line >= active_lines-1) exp_line <= '0;
        else                            exp_line <= exp_line + 1'b1;
      end else begin
        exp_pixel <= exp_pixel + 1'b1;
        exp_line  <= exp_line;
      end
    end
  end

  // Basic legality of configuration
  assert property (@(posedge aclk) active_pixels > 0 && active_lines > 0);

  // axis_tvalid must be constantly 1
  assert property (@(posedge aclk) axis_tvalid);

  // Reset values
  assert property (@(posedge aclk) rst |-> (!axis_tlast && !axis_tuser_sof && !axis_tuser_pulse &&
                                           (fid == (INTERLACE ? 1'b1 : 1'b0))));

  // Hold behavior when not ready
  assert property (@(posedge aclk) disable iff (rst)
    !axis_tready |-> $stable({axis_tlast, axis_tuser_sof, axis_tuser_pulse, fid, axis_tdata_video})
  );

  // EOL and SOF outputs vs reference (use previous expected counters)
  assert property (@(posedge aclk) disable iff (rst)
    axis_tready |-> axis_tlast == ($past(exp_pixel) == active_pixels-1)
  );

  assert property (@(posedge aclk) disable iff (rst)
    axis_tready |-> axis_tuser_sof == (($past(exp_pixel) == 0) && ($past(exp_line) == 0))
  );

  // axis_tuser_pulse must assert on rising EOL captured with ready, only for one cycle
  assert property (@(posedge aclk) disable iff (rst)
    axis_tready && (($past(exp_pixel) == active_pixels-1) &&
                    !($past($past(exp_pixel)) == $past(active_pixels)-1))
    |-> axis_tuser_pulse
  );

  assert property (@(posedge aclk) disable iff (rst)
    axis_tready && axis_tuser_pulse |->
      (($past(exp_pixel) == active_pixels-1) &&
       !($past($past(exp_pixel)) == $past(active_pixels)-1))
  );

  assert property (@(posedge aclk) disable iff (rst)
    axis_tuser_pulse |-> !$past(axis_tuser_pulse)
  );

  // Interlace/FID behavior
  generate
    if (INTERLACE) begin
      // FID toggles only on SOF with ready; otherwise stable
      assert property (@(posedge aclk) disable iff (rst)
        axis_tready && axis_tuser_sof |-> $changed(fid)
      );
      assert property (@(posedge aclk) disable iff (rst)
        axis_tready && !axis_tuser_sof |-> $stable(fid)
      );
    end else begin
      // Non-interlaced: FID always 0; data never inverted
      assert property (@(posedge aclk) disable iff (rst) fid == 1'b0);
    end
  endgenerate

  // Data mapping check (using settled fid after sequential updates)
  localparam int PIXW  = 12;
  localparam int LINEW = 14;
  localparam int EXPW  = PIXW + LINEW; // 26

  logic [EXPW-1:0] ref_norm, ref_inv, ref_data;
  always_comb begin
    ref_norm = {exp_line, exp_pixel[PIXW-1:0]};
    ref_inv  = {~exp_line, ~exp_pixel[PIXW-1:0]};
    ref_data = (INTERLACE && fid) ? ref_inv : ref_norm;
  end

  generate
    if (DATA_WIDTH < EXPW) begin
      assert property (@(posedge aclk) disable iff (rst)
        axis_tready |-> axis_tdata_video == ref_data[DATA_WIDTH-1:0]
      );
    end else if (DATA_WIDTH == EXPW) begin
      assert property (@(posedge aclk) disable iff (rst)
        axis_tready |-> axis_tdata_video == ref_data
      );
    end else begin
      assert property (@(posedge aclk) disable iff (rst)
        axis_tready |-> (axis_tdata_video[EXPW-1:0] == ref_data &&
                         axis_tdata_video[DATA_WIDTH-1:EXPW] == '0)
      );
    end
  endgenerate

  // Optional: inputs stable during a frame (allow change only at SOF)
  assert property (@(posedge aclk) disable iff (rst)
    axis_tready && !axis_tuser_sof |-> ($stable(active_pixels) && $stable(active_lines))
  );

  // Frame wrap: last pixel of last line leads to SOF on next ready
  assert property (@(posedge aclk) disable iff (rst)
    axis_tready &&
    ($past(exp_pixel) == active_pixels-1) &&
    ($past(exp_line)  >= active_lines-1)
    |-> ##1 (axis_tready && axis_tuser_sof)
  );

  // Coverage
  cover property (@(posedge aclk) disable iff (rst) axis_tready && axis_tuser_sof);
  cover property (@(posedge aclk) disable iff (rst) axis_tready && axis_tlast);
  cover property (@(posedge aclk) disable iff (rst) axis_tready && axis_tuser_pulse);
  cover property (@(posedge aclk) disable iff (rst)
    axis_tready && ($past(exp_pixel) == active_pixels-1) && ($past(exp_line) >= active_lines-1)
    ##1 axis_tready && axis_tuser_sof
  );
  cover property (@(posedge aclk) disable iff (rst) !axis_tready ##1 axis_tready);
  generate
    if (INTERLACE) begin
      cover property (@(posedge aclk) disable iff (rst) axis_tready && fid);
      cover property (@(posedge aclk) disable iff (rst) axis_tready && !fid);
    end
  endgenerate

endmodule

// Bind to DUT
bind axis_gen_pulse axis_gen_pulse_sva #(
  .DLY(DLY), .INTERLACE(INTERLACE), .DATA_WIDTH(DATA_WIDTH)
) axis_gen_pulse_sva_i (
  .aclk(aclk),
  .rst(rst),
  .axis_tready(axis_tready),
  .axis_tvalid(axis_tvalid),
  .axis_tdata_video(axis_tdata_video),
  .axis_tlast(axis_tlast),
  .fid(fid),
  .axis_tuser_sof(axis_tuser_sof),
  .axis_tuser_pulse(axis_tuser_pulse),
  .active_pixels(active_pixels),
  .active_lines(active_lines)
);