// SVA for adapter_block_fifo_2_axi_stream
// Bind into DUT to check key protocol/functional invariants and provide coverage

module adapter_block_fifo_2_axi_stream_sva #(
  parameter int DATA_WIDTH   = 24,
  parameter bit USER_IN_DATA = 1
)(
  input  logic                        i_axi_clk,
  input  logic                        rst,

  input  logic                        i_block_fifo_rdy,
  input  logic                        o_block_fifo_act,
  input  logic [23:0]                 i_block_fifo_size,
  input  logic [DATA_WIDTH:0]         i_block_fifo_data,
  input  logic                        o_block_fifo_stb,

  input  logic [3:0]                  i_axi_user,
  input  logic [3:0]                  o_axi_user,
  input  logic                        i_axi_ready,
  input  logic [DATA_WIDTH-1:0]       o_axi_data,
  input  logic                        o_axi_last,
  input  logic                        o_axi_valid,

  input  logic [31:0]                 o_debug,

  // internal DUT state/regs
  input  logic [3:0]                  state,
  input  logic [23:0]                 r_count
);
  localparam int IDLE    = 0;
  localparam int READY   = 1;
  localparam int RELEASE = 2;

  default clocking cb @(posedge i_axi_clk); endclocking
  default disable iff (rst);

  // Reset behavior (synchronous)
  assert property (@(posedge i_axi_clk) rst |=> state==IDLE && !o_block_fifo_act && r_count==24'd0 && !o_axi_valid);

  // State encoding valid
  assert property (state inside {IDLE,READY,RELEASE});

  // Handshake/strobe definition must match
  assert property (o_block_fifo_stb == (i_axi_ready && o_axi_valid));

  // o_axi_data mapping
  assert property (o_axi_data == i_block_fifo_data[DATA_WIDTH-1:0]);

  // USER mapping
  generate
    if (USER_IN_DATA) begin : g_user_in_data
      assert property (o_axi_user[3:1] == 3'b000);
      assert property ((r_count < i_block_fifo_size) |-> (o_axi_user[0] == i_block_fifo_data[DATA_WIDTH]));
      assert property ((r_count >= i_block_fifo_size) |-> (o_axi_user[0] == 1'b0));
    end else begin : g_user_passthru
      assert property (o_axi_user == i_axi_user);
    end
  endgenerate

  // Size must be stable while a block is active
  assert property (o_block_fifo_act |-> $stable(i_block_fifo_size));

  // IDLE -> READY start condition
  assert property (state==IDLE && i_block_fifo_rdy && !o_block_fifo_act |=> state==READY && o_block_fifo_act && r_count==24'd0);

  // READY implies active; non-READY implies not active
  assert property (state==READY |-> o_block_fifo_act);
  assert property ((state!=READY) |-> !o_block_fifo_act);

  // VALID only when in READY
  assert property ((state!=READY) |-> !o_axi_valid);

  // r_count monotonic and handshake-driven while READY
  assert property (state==READY && !o_block_fifo_stb |=> r_count == $past(r_count));
  assert property (state==READY && o_block_fifo_stb && (r_count < i_block_fifo_size) |=> r_count == $past(r_count)+24'd1);

  // r_count never exceeds size
  assert property (r_count <= i_block_fifo_size);

  // LAST semantics tied to count and activity/valid
  assert property (o_axi_last |-> o_axi_valid && o_block_fifo_act && ((r_count + 24'd1) >= i_block_fifo_size));
  assert property (o_block_fifo_act && o_axi_valid && ((r_count + 24'd1) >= i_block_fifo_size) |-> o_axi_last);

  // After last-beat handshake, block releases and returns to IDLE
  assert property (o_block_fifo_stb && o_axi_last |=> !o_block_fifo_act && state==RELEASE ##1 state==IDLE);

  // READY done (count reached size) -> RELEASE next
  assert property (state==READY && (r_count == i_block_fifo_size) |=> state==RELEASE && !o_block_fifo_act && !o_axi_valid);

  // Debug mapping (basic)
  assert property (o_debug[3:0] == state);
  assert property (o_debug[5]   == o_block_fifo_act);

  // Coverage: basic block with backpressure then completion
  cover property (
    state==IDLE && i_block_fifo_rdy ##1
    state==READY && o_axi_valid && !i_axi_ready [*1:$] ##1
    o_block_fifo_stb && !o_axi_last [*1:$] ##1
    o_block_fifo_stb && o_axi_last ##1
    state==RELEASE ##1 state==IDLE
  );

  // Coverage: single-beat transfer (size==1)
  cover property (
    state==IDLE && i_block_fifo_rdy && (i_block_fifo_size==24'd1) ##1
    state==READY ##1
    o_block_fifo_stb && o_axi_last ##1 state==RELEASE ##1 state==IDLE
  );

  // Coverage: multi-beat transfer (size>=2)
  cover property (
    state==IDLE && i_block_fifo_rdy && (i_block_fifo_size>=24'd2) ##1
    state==READY ##1
    o_block_fifo_stb && !o_axi_last ##1
    o_block_fifo_stb && o_axi_last
  );

endmodule


// Bind into DUT
bind adapter_block_fifo_2_axi_stream
  adapter_block_fifo_2_axi_stream_sva #(
    .DATA_WIDTH(DATA_WIDTH),
    .USER_IN_DATA(USER_IN_DATA)
  ) u_adapter_block_fifo_2_axi_stream_sva (
    .i_axi_clk        (i_axi_clk),
    .rst              (rst),

    .i_block_fifo_rdy (i_block_fifo_rdy),
    .o_block_fifo_act (o_block_fifo_act),
    .i_block_fifo_size(i_block_fifo_size),
    .i_block_fifo_data(i_block_fifo_data),
    .o_block_fifo_stb (o_block_fifo_stb),

    .i_axi_user       (i_axi_user),
    .o_axi_user       (o_axi_user),
    .i_axi_ready      (i_axi_ready),
    .o_axi_data       (o_axi_data),
    .o_axi_last       (o_axi_last),
    .o_axi_valid      (o_axi_valid),

    .o_debug          (o_debug),

    .state            (state),
    .r_count          (r_count)
  );