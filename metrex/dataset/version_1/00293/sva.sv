// SVA for tmu2_decay
// Concise, focuses on protocol, pipeline control, chroma-key gating, and datapath correctness.

module tmu2_decay_sva #(
  parameter fml_depth = 26
) (
  input  logic                   sys_clk,
  input  logic                   sys_rst,

  // DUT ports
  input  logic                   busy,
  input  logic [5:0]             brightness,
  input  logic                   chroma_key_en,
  input  logic [15:0]            chroma_key,
  input  logic                   pipe_stb_i,
  input  logic                   pipe_ack_i,
  input  logic [15:0]            color,
  input  logic [fml_depth-1-1:0] dadr,
  input  logic                   pipe_stb_o,
  input  logic                   pipe_ack_o,
  input  logic [15:0]            color_d,
  input  logic [fml_depth-1-1:0] dadr_f,

  // DUT internals we assert on
  input  logic                   en,
  input  logic                   valid_1,
  input  logic                   valid_2
);

  default clocking cb @(posedge sys_clk); endclocking

  // Reset values (synchronous)
  assert property (@(posedge sys_clk)
    sys_rst |-> (!busy && !pipe_stb_o && pipe_ack_o && (valid_1==1'b0) && (valid_2==1'b0)));

  // Combinational relations
  assert property (pipe_ack_o == en);
  assert property (en == (~valid_2 | pipe_ack_i));
  assert property (pipe_stb_o == valid_2);
  assert property (busy == (valid_1 | valid_2));
  assert property ((!valid_2) |-> pipe_ack_o);                 // ready when not holding output
  assert property ((valid_2) |-> (pipe_ack_o == pipe_ack_i && en == pipe_ack_i));

  // Registers hold when !en
  assert property (disable iff (sys_rst) (!en) |-> $stable({valid_1, valid_2, color_d, dadr_f}));

  // Valid pipeline updates (1-cycle)
  assert property (disable iff (sys_rst) 1'b1 |=> (valid_2 == $past(en ? valid_1 : valid_2)));
  assert property (disable iff (sys_rst) 1'b1 |=> (valid_1 == $past(en ? (pipe_stb_i & ((color != chroma_key) | ~chroma_key_en)) : valid_1)));

  // Output must be held under backpressure until ack
  assert property (disable iff (sys_rst)
    pipe_stb_o && !pipe_ack_i |-> (pipe_stb_o && $stable({color_d,dadr_f})) until_with pipe_ack_i);

  // Chroma-key drop: if previous stage empty and current sample is keyed, no output next cycle
  assert property (disable iff (sys_rst)
    en && $past(en) && !$past(valid_1) && $past(pipe_stb_i && chroma_key_en && (color == chroma_key))
    |-> !pipe_stb_o);

  // Functional datapath check: accept -> output (1 cycle latency with consecutive en)
  // Expected color_d computed from past color/brightness:
  // scale = {1'b0,brightness}+1; color_d = { (scale*r)[10:6], (scale*g)[11:6], (scale*b)[10:6] }
  assert property (disable iff (sys_rst)
    en && $past(en) &&
    $past(pipe_stb_i & ((color != chroma_key) | ~chroma_key_en))
    |->
    ( pipe_stb_o
      && color_d == {
           ((({1'b0,$past(brightness)} + 7'd1) * $past(color[15:11]))[10:6]),
           ((({1'b0,$past(brightness)} + 7'd1) * $past(color[10:5])) [11:6]),
           ((({1'b0,$past(brightness)} + 7'd1) * $past(color[4:0]))  [10:6])
         }
      && dadr_f == $past(dadr)
    )
  );

  // If output was the only valid and got acked, it must clear next cycle
  assert property (disable iff (sys_rst)
    valid_2 && !valid_1 && pipe_ack_i |=> !valid_2);

  // Sanity: no X on primary outputs/controls in non-reset
  assert property (disable iff (sys_rst)
    !$isunknown({busy,pipe_stb_o,pipe_ack_o,color_d,dadr_f,valid_1,valid_2,en}));

  // Coverage

  // Accept and flow through normally
  cover property (disable iff (sys_rst)
    en && $past(en) &&
    $past(pipe_stb_i & ((color != chroma_key) | ~chroma_key_en)) |->
    pipe_stb_o && pipe_ack_i);

  // Downstream backpressure then release
  cover property (disable iff (sys_rst)
    pipe_stb_o && !pipe_ack_i ##1 !pipe_ack_i ##1 pipe_ack_i);

  // Chroma-key drop event (with empty prev stage)
  cover property (disable iff (sys_rst)
    en && $past(en) && !$past(valid_1) &&
    $past(pipe_stb_i && chroma_key_en && (color == chroma_key)) ##1 !pipe_stb_o);

  // Brightness extremes exercised with acceptance
  cover property (disable iff (sys_rst)
    pipe_stb_i && (brightness==6'd0) && ((color != chroma_key) | ~chroma_key_en));
  cover property (disable iff (sys_rst)
    pipe_stb_i && (brightness==6'd63) && ((color != chroma_key) | ~chroma_key_en));

endmodule

// Bind into the DUT
bind tmu2_decay tmu2_decay_sva #(.fml_depth(fml_depth)) tmu2_decay_sva_i (
  .sys_clk(sys_clk),
  .sys_rst(sys_rst),
  .busy(busy),
  .brightness(brightness),
  .chroma_key_en(chroma_key_en),
  .chroma_key(chroma_key),
  .pipe_stb_i(pipe_stb_i),
  .pipe_ack_i(pipe_ack_i),
  .color(color),
  .dadr(dadr),
  .pipe_stb_o(pipe_stb_o),
  .pipe_ack_o(pipe_ack_o),
  .color_d(color_d),
  .dadr_f(dadr_f),
  .en(en),
  .valid_1(valid_1),
  .valid_2(valid_2)
);