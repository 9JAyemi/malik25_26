// SVA for adapter_rgb_2_ppfifo
module adapter_rgb_2_ppfifo_sva #(parameter DATA_WIDTH=24) (
  input  logic                      clk,
  input  logic                      rst,
  input  logic [23:0]               i_rgb,
  input  logic                      i_h_blank,
  input  logic [1:0]                i_ppfifo_rdy,
  input  logic [23:0]               i_ppfifo_size,
  input  logic                      o_ppfifo_clk,
  input  logic [1:0]                o_ppfifo_act,
  input  logic                      o_ppfifo_stb,
  input  logic [DATA_WIDTH-1:0]     o_ppfifo_data,
  input  logic [2:0]                state,
  input  logic [23:0]               r_count
);

  localparam int IDLE    = 0;
  localparam int READY   = 1;
  localparam int RELEASE = 2;

  // Clock passthrough
  assert property (@(posedge clk)  o_ppfifo_clk) else $error("o_ppfifo_clk not high on posedge clk");
  assert property (@(negedge clk) !o_ppfifo_clk) else $error("o_ppfifo_clk not low on negedge clk");

  // Reset behavior
  assert property (@(posedge clk) rst |=> (state==IDLE && o_ppfifo_act==2'b00 && r_count==0 && !o_ppfifo_stb));

  // FSM legal states
  assert property (@(posedge clk) disable iff (rst) state inside {IDLE,READY,RELEASE});

  // Handshake from IDLE to READY requires rdy>0 and picks proper channel; r_count reset
  assert property (@(posedge clk) disable iff (rst)
    (state==IDLE && (i_ppfifo_rdy!=0)) |=> (state==READY));
  assert property (@(posedge clk) disable iff (rst)
    $rose(state==READY) |-> ($past(i_ppfifo_rdy)!=0 && r_count==0));
  // Priority select: bit0 over bit1 when both ready
  assert property (@(posedge clk) disable iff (rst)
    $rose(state==READY) |-> ( ($past(i_ppfifo_rdy[0]) && o_ppfifo_act==2'b01) ||
                              (!$past(i_ppfifo_rdy[0]) && $past(i_ppfifo_rdy[1]) && o_ppfifo_act==2'b10) ));

  // o_ppfifo_act encoding and stability
  assert property (@(posedge clk) disable iff (rst) $onehot0(o_ppfifo_act));
  assert property (@(posedge clk) disable iff (rst) (state==IDLE)  |-> (o_ppfifo_act==2'b00));
  assert property (@(posedge clk) disable iff (rst) (state==READY) |-> (o_ppfifo_act!=2'b00 && $onehot(o_ppfifo_act) && $stable(o_ppfifo_act)));

  // READY data/strobe/count behavior
  assert property (@(posedge clk) disable iff (rst)
    (state==READY && !i_h_blank && (r_count < i_ppfifo_size)) |-> (o_ppfifo_stb && (o_ppfifo_data==i_rgb) && (r_count==$past(r_count)+1)));
  assert property (@(posedge clk) disable iff (rst)
    (state==READY && (i_h_blank || !(r_count < i_ppfifo_size))) |-> !o_ppfifo_stb);

  // r_count monotonic while staying in READY
  assert property (@(posedge clk) disable iff (rst)
    (state==READY && $past(state==READY)) |-> (r_count==$past(r_count) || r_count==$past(r_count)+1));

  // RELEASE conditions and transitions
  assert property (@(posedge clk) disable iff (rst)
    (state==READY && (r_count >= i_ppfifo_size)) |=> (state==RELEASE));
  assert property (@(posedge clk) disable iff (rst)
    (state==READY && (r_count>0) && i_h_blank) |=> (state==RELEASE));
  assert property (@(posedge clk) disable iff (rst)
    (state==READY && (r_count==0) && i_h_blank) |=> (state==READY));
  assert property (@(posedge clk) disable iff (rst)
    (state==RELEASE) |-> (o_ppfifo_act==2'b00));
  assert property (@(posedge clk) disable iff (rst)
    (state==RELEASE) |=> (state==IDLE && o_ppfifo_act==2'b00));

  // Strobe only allowed in READY when not blank and count < size
  assert property (@(posedge clk) disable iff (rst)
    o_ppfifo_stb |-> (state==READY && !i_h_blank && (r_count < i_ppfifo_size)));

  // Data holds when not strobing
  assert property (@(posedge clk) disable iff (rst)
    !o_ppfifo_stb |-> $stable(o_ppfifo_data));

  // -------- Coverage --------
  // Basic transaction path
  cover property (@(posedge clk) disable iff (rst)
    (state==IDLE && i_ppfifo_rdy!=0) ##1 (state==READY) ##[1:$] (state==RELEASE) ##1 (state==IDLE));

  // Channel 0 selection
  cover property (@(posedge clk) disable iff (rst)
    (state==IDLE && i_ppfifo_rdy==2'b01) ##1 (state==READY && o_ppfifo_act==2'b01));

  // Channel 1 selection
  cover property (@(posedge clk) disable iff (rst)
    (state==IDLE && i_ppfifo_rdy==2'b10) ##1 (state==READY && o_ppfifo_act==2'b10));

  // Both ready -> channel 0 priority
  cover property (@(posedge clk) disable iff (rst)
    (state==IDLE && i_ppfifo_rdy==2'b11) ##1 (state==READY && o_ppfifo_act==2'b01));

  // Early release by blanking after at least one beat
  cover property (@(posedge clk) disable iff (rst)
    (state==READY && !i_h_blank && (r_count < i_ppfifo_size) && o_ppfifo_stb)
    ##1 (state==READY && i_h_blank && r_count>0)
    ##1 (state==RELEASE));

  // Size-based release
  cover property (@(posedge clk) disable iff (rst)
    (state==READY && r_count==i_ppfifo_size) ##1 (state==RELEASE));

  // Zero-size transfer (no strobes)
  cover property (@(posedge clk) disable iff (rst)
    (state==IDLE && i_ppfifo_rdy!=0 && i_ppfifo_size==0) ##1 (state==READY) ##1 (state==RELEASE));
endmodule

// Bind into DUT
bind adapter_rgb_2_ppfifo adapter_rgb_2_ppfifo_sva #(.DATA_WIDTH(DATA_WIDTH)) u_adapter_rgb_2_ppfifo_sva (
  .clk(clk),
  .rst(rst),
  .i_rgb(i_rgb),
  .i_h_blank(i_h_blank),
  .i_ppfifo_rdy(i_ppfifo_rdy),
  .i_ppfifo_size(i_ppfifo_size),
  .o_ppfifo_clk(o_ppfifo_clk),
  .o_ppfifo_act(o_ppfifo_act),
  .o_ppfifo_stb(o_ppfifo_stb),
  .o_ppfifo_data(o_ppfifo_data),
  .state(state),
  .r_count(r_count)
);