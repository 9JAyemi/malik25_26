// SVA checker for adapter_axi_stream_2_ppfifo_wl
// Focused, high-quality properties with essential coverage

module adapter_axi_stream_2_ppfifo_wl_sva #(
  parameter int DATA_WIDTH   = 32,
  parameter int STROBE_WIDTH = DATA_WIDTH/8,
  parameter int USE_KEEP     = 0
)(
  input  logic                        clk,
  input  logic                        rst,

  input  logic                        i_tear_effect,
  input  logic                        i_fsync,
  input  logic [31:0]                 i_pixel_count,

  input  logic                        o_axi_ready,
  input  logic [DATA_WIDTH-1:0]       i_axi_data,
  input  logic [STROBE_WIDTH-1:0]     i_axi_keep,
  input  logic                        i_axi_last,
  input  logic                        i_axi_valid,

  input  logic                        o_ppfifo_clk,
  input  logic [1:0]                  i_ppfifo_rdy,
  input  logic [1:0]                  o_ppfifo_act,
  input  logic [23:0]                 i_ppfifo_size,
  input  logic                        o_ppfifo_stb,
  input  logic [DATA_WIDTH:0]         o_ppfifo_data,

  // internal taps
  input  logic [3:0]                  state,
  input  logic [23:0]                 r_count,
  input  logic                        r_last,
  input  logic [31:0]                 r_pixel_count,
  input  logic                        r_prev_tear,
  input  logic                        r_pos_edge_tear
);

  localparam int WAIT_FOR_TEAR_EFFECT = 0;
  localparam int WAIT_FOR_FRAME       = 1;
  localparam int READ_FRAME           = 2;
  localparam int WAIT_FOR_END_TEAR    = 3;

  localparam int TEAR_WINDOW_COUNT    = 100;

  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Structural/basic
  assert property (o_ppfifo_clk == clk);
  assert property ($onehot0(o_ppfifo_act));

  // Ready definition must match RTL expression
  assert property (
    o_axi_ready == ((|o_ppfifo_act) && (r_count < i_ppfifo_size) && !r_last && (state == READ_FRAME))
  );

  // AXI4-Stream sink: data must be stable while valid && !ready
  assert property (i_axi_valid && !o_axi_ready |-> $stable({i_axi_data,i_axi_keep,i_axi_last}));

  // Handshake -> write strobe and data mapping (same cycle)
  property hand; (state==READ_FRAME && (|o_ppfifo_act) && i_axi_valid && o_axi_ready); endproperty
  assert property (hand |-> o_ppfifo_stb
                          && (o_ppfifo_data[DATA_WIDTH-1:0] == i_axi_data)
                          && (o_ppfifo_data[DATA_WIDTH]     == i_axi_last));

  // Handshake -> counters/flags update (next cycle)
  assert property (hand |=> (r_count       == $past(r_count) + 1)
                           && (r_pixel_count == $past(r_pixel_count) + 1)
                           && (r_last        == $past(i_axi_last)));

  // No write without handshake
  assert property (o_ppfifo_stb |-> hand);

  // r_count bounded while active
  assert property ((state==READ_FRAME && |o_ppfifo_act) |-> (r_count <= i_ppfifo_size));

  // Activate ppfifo bank when ready and currently inactive
  assert property ((!(|o_ppfifo_act) && i_ppfifo_rdy[0]) |=> (o_ppfifo_act == 2'b01));
  assert property ((!(|o_ppfifo_act) && !i_ppfifo_rdy[0] && i_ppfifo_rdy[1]) |=> (o_ppfifo_act == 2'b10));

  // Deactivate on last or on size reached
  assert property ((state==READ_FRAME && |o_ppfifo_act && r_last) |=> (o_ppfifo_act == 2'b00));
  assert property ((state==READ_FRAME && |o_ppfifo_act && (r_count >= i_ppfifo_size)) |=> (o_ppfifo_act == 2'b00));

  // Tear-effect edge detection and consumption
  assert property ($rose(i_tear_effect) |=> r_pos_edge_tear);
  assert property ((state==WAIT_FOR_TEAR_EFFECT && r_pos_edge_tear)
                   |=> (state==WAIT_FOR_FRAME && !r_pos_edge_tear && r_pixel_count==0));
  assert property ((state==WAIT_FOR_TEAR_EFFECT && !r_pos_edge_tear) |=> state==WAIT_FOR_TEAR_EFFECT);

  // Frame wait window behavior
  assert property ((state==WAIT_FOR_FRAME && i_fsync)
                   |=> (state==READ_FRAME && r_pixel_count==0));
  assert property ((state==WAIT_FOR_FRAME && !i_fsync && (r_pixel_count < TEAR_WINDOW_COUNT))
                   |=> (state==WAIT_FOR_FRAME && r_pixel_count == $past(r_pixel_count)+1));
  assert property ((state==WAIT_FOR_FRAME && !i_fsync && (r_pixel_count >= TEAR_WINDOW_COUNT))
                   |=> (state==WAIT_FOR_TEAR_EFFECT));

  // End-of-frame transition to WAIT_FOR_END_TEAR
  assert property ((state==READ_FRAME && |o_ppfifo_act && r_last && (r_pixel_count >= i_pixel_count))
                   |=> (state==WAIT_FOR_END_TEAR));

  // Exit WAIT_FOR_END_TEAR only when tear_effect deasserts
  assert property ((state==WAIT_FOR_END_TEAR && !i_tear_effect) |=> (state==WAIT_FOR_TEAR_EFFECT));

  // Reset post-conditions (one cycle after rising edge)
  assert property ($rose(rst) |=> (state==WAIT_FOR_TEAR_EFFECT
                                  && r_count==0
                                  && o_ppfifo_act==2'b00
                                  && r_pixel_count==0
                                  && r_pos_edge_tear==0));

  // Coverage
  cover property (state==WAIT_FOR_TEAR_EFFECT);
  cover property (state==WAIT_FOR_FRAME);
  cover property (state==READ_FRAME);
  cover property (state==WAIT_FOR_END_TEAR);

  cover property (hand);                              // any transfer
  cover property (hand && i_axi_last);                // last beat transfer
  cover property (!|o_ppfifo_act ##1 i_ppfifo_rdy[0] ##1 (o_ppfifo_act==2'b01)); // bank0 use
  cover property (!|o_ppfifo_act ##1 (!i_ppfifo_rdy[0] && i_ppfifo_rdy[1]) ##1 (o_ppfifo_act==2'b10)); // bank1 use
  cover property ((state==WAIT_FOR_FRAME && (r_pixel_count==TEAR_WINDOW_COUNT)) ##1 (state==WAIT_FOR_TEAR_EFFECT)); // timeout path
  cover property ((state==READ_FRAME && |o_ppfifo_act && i_axi_valid && o_axi_ready && i_axi_last
                   && (r_pixel_count >= i_pixel_count)) ##1 (state==WAIT_FOR_END_TEAR)); // EoF to end-tear
endmodule

// Bind into DUT
bind adapter_axi_stream_2_ppfifo_wl
  adapter_axi_stream_2_ppfifo_wl_sva #(
    .DATA_WIDTH(DATA_WIDTH),
    .STROBE_WIDTH(STROBE_WIDTH),
    .USE_KEEP(USE_KEEP)
  ) i_adapter_axi_stream_2_ppfifo_wl_sva (
    .clk             (i_axi_clk),
    .rst             (rst),

    .i_tear_effect   (i_tear_effect),
    .i_fsync         (i_fsync),
    .i_pixel_count   (i_pixel_count),

    .o_axi_ready     (o_axi_ready),
    .i_axi_data      (i_axi_data),
    .i_axi_keep      (i_axi_keep),
    .i_axi_last      (i_axi_last),
    .i_axi_valid     (i_axi_valid),

    .o_ppfifo_clk    (o_ppfifo_clk),
    .i_ppfifo_rdy    (i_ppfifo_rdy),
    .o_ppfifo_act    (o_ppfifo_act),
    .i_ppfifo_size   (i_ppfifo_size),
    .o_ppfifo_stb    (o_ppfifo_stb),
    .o_ppfifo_data   (o_ppfifo_data),

    .state           (state),
    .r_count         (r_count),
    .r_last          (r_last),
    .r_pixel_count   (r_pixel_count),
    .r_prev_tear     (r_prev_tear),
    .r_pos_edge_tear (r_pos_edge_tear)
  );