// SVA for serializer
// Bind-friendly, concise, and focused on key behaviors

module serializer_sva #(
  parameter LOG_DWIDTH = 7,
  parameter DWIDTH     = 64
)(
  input  wire                 clk,
  input  wire                 fast_clk,
  input  wire [DWIDTH-1:0]    data_in,
  input  wire [DWIDTH-1:0]    buffer,     // DUT internal
  input  wire [LOG_DWIDTH-1:0] curr_bit,  // DUT internal
  input  wire                 clk_d1,     // DUT internal
  input  wire                 data_out
);

  // Static sanity: index space must cover DWIDTH
  initial assert ((1 << LOG_DWIDTH) >= DWIDTH)
    else $error("serializer: LOG_DWIDTH too small for DWIDTH");

  // Slow-domain capture: buffer follows data_in on clk edge
  assert property (@(posedge clk) 1'b1 |=> buffer == $past(data_in));

  // Cross-check in fast domain at frame start
  assert property (@(posedge fast_clk) $rose(clk) |=> buffer == $past(data_in));

  // Fast-domain sampling of clk and edge detection correctness
  assert property (@(posedge fast_clk) clk_d1 == $past(clk));
  assert property (@(posedge fast_clk) ((!clk_d1 && clk) == $rose(clk)));

  // curr_bit control: reset on slow clk rise; otherwise increment by 1
  assert property (@(posedge fast_clk) $rose(clk) |=> curr_bit == '0);
  assert property (@(posedge fast_clk) !$rose(clk) |=> curr_bit == $past(curr_bit) + 1'b1);

  // Optional: enforce exactly DWIDTH fast cycles per slow frame
  assert property (@(posedge fast_clk)
    $rose(clk) |=> (! $rose(clk))[* (DWIDTH-1)] ##1 $rose(clk));

  // Index must never exceed DWIDTH-1 (prevents out-of-range select)
  assert property (@(posedge fast_clk) curr_bit < DWIDTH);

  // Output must match selected buffer bit (both domains)
  assert property (@(posedge fast_clk) data_out == buffer[curr_bit]);
  assert property (@(posedge clk)      data_out == buffer[curr_bit]);

  // Coverage: observe a full frame from bit 0 to bit DWIDTH-1 then next frame edge
  cover property (@(posedge fast_clk)
    $rose(clk) ##1 (curr_bit == '0)
    ##(DWIDTH-1) (curr_bit == (DWIDTH-1)) ##1 $rose(clk));

endmodule

// Bind into DUT (accessing internals)
bind serializer serializer_sva #(.LOG_DWIDTH(LOG_DWIDTH), .DWIDTH(DWIDTH)) sva_i (
  .clk(clk),
  .fast_clk(fast_clk),
  .data_in(data_in),
  .buffer(buffer),
  .curr_bit(curr_bit),
  .clk_d1(clk_d1),
  .data_out(data_out)
);