// SVA for serial_tx
// Bindable, concise, and focused on functional correctness and coverage.

module serial_tx_sva #(
  parameter int CLK_PER_BIT = 50,
  parameter int CTR_SIZE    = 6
)(
  input  logic                   clk,
  input  logic                   rst,
  // DUT I/Os
  input  logic                   tx,
  input  logic                   busy,
  input  logic                   block,
  input  logic [7:0]             data,
  input  logic                   new_data,
  // DUT internals (for deep checks)
  input  logic [CTR_SIZE-1:0]    ctr_q,
  input  logic [2:0]             bit_ctr_q,
  input  logic [7:0]             data_q,
  input  logic [1:0]             state_q,
  input  logic                   block_q
);

  localparam int IDLE      = 2'd0;
  localparam int START_BIT = 2'd1;
  localparam int DATA      = 2'd2;
  localparam int STOP_BIT  = 2'd3;

  localparam int END_VAL   = CLK_PER_BIT-1;

  // Static parameter sanity
  initial begin
    assert (CLK_PER_BIT > 0) else $error("CLK_PER_BIT must be > 0");
    assert (CLK_PER_BIT <= (1<<CTR_SIZE)) else $error("CLK_PER_BIT exceeds counter range");
  end

  // Basic well-formedness
  assert property (@(posedge clk) state_q inside {IDLE,START_BIT,DATA,STOP_BIT});
  assert property (@(posedge clk) disable iff (rst) !$isunknown({state_q,tx,busy,block_q,ctr_q,bit_ctr_q}));

  // Reset behavior
  assert property (@(posedge clk) rst |-> (state_q==IDLE && tx==1'b1));

  // Busy semantics
  assert property (@(posedge clk) disable iff (rst) (state_q!=IDLE) |-> busy);
  assert property (@(posedge clk) disable iff (rst)
    (state_q==IDLE && !block_q && !new_data && $past(state_q==IDLE && !block_q && !new_data))
    |-> !busy);

  // Line level by state
  assert property (@(posedge clk) disable iff (rst) (state_q==START_BIT) |-> (tx==1'b0));
  assert property (@(posedge clk) disable iff (rst) (state_q==STOP_BIT || state_q==IDLE) |-> (tx==1'b1));

  // Block keeps IDLE (no unintended start)
  assert property (@(posedge clk) disable iff (rst) (state_q==IDLE && block_q) |=> (state_q==IDLE && tx==1'b1 && busy));

  // Accept new_data when unblocked IDLE
  sequence accept;
    state_q==IDLE && !block_q && new_data;
  endsequence
  assert property (@(posedge clk) disable iff (rst)
    accept |=> (state_q==START_BIT && busy && tx==1'b0 && ctr_q==0 && bit_ctr_q==0 && data_q==$past(data)));

  // START_BIT timing and transition
  assert property (@(posedge clk) disable iff (rst)
    (state_q==START_BIT && $past(state_q)!=START_BIT) |-> (ctr_q==0 && tx==0));
  assert property (@(posedge clk) disable iff (rst)
    (state_q==START_BIT && ctr_q!=END_VAL) |=> (state_q==START_BIT && tx==0 && ctr_q==$past(ctr_q)+1));
  assert property (@(posedge clk) disable iff (rst)
    (state_q==START_BIT && ctr_q==END_VAL) |=> (state_q==DATA && ctr_q==0));

  // DATA entry
  assert property (@(posedge clk) disable iff (rst)
    (state_q==DATA && $past(state_q)!=DATA) |-> (bit_ctr_q==0 && ctr_q==0));

  // DATA bit hold and counter progression
  assert property (@(posedge clk) disable iff (rst)
    (state_q==DATA) |-> (tx==data_q[bit_ctr_q]));
  assert property (@(posedge clk) disable iff (rst)
    (state_q==DATA && ctr_q!=END_VAL) |=> (state_q==DATA && ctr_q==$past(ctr_q)+1 && bit_ctr_q==$past(bit_ctr_q)));

  // DATA end-of-bit transitions
  assert property (@(posedge clk) disable iff (rst)
    (state_q==DATA && ctr_q==END_VAL && bit_ctr_q!=3'd7)
    |=> (state_q==DATA && ctr_q==0 && bit_ctr_q==$past(bit_ctr_q)+1));
  assert property (@(posedge clk) disable iff (rst)
    (state_q==DATA && ctr_q==END_VAL && bit_ctr_q==3'd7)
    |=> (state_q==STOP_BIT && ctr_q==0));

  // STOP_BIT timing and transition
  assert property (@(posedge clk) disable iff (rst)
    (state_q==STOP_BIT && $past(state_q)!=STOP_BIT) |-> (tx==1));
  assert property (@(posedge clk) disable iff (rst)
    (state_q==STOP_BIT && ctr_q!=END_VAL) |=> (state_q==STOP_BIT && tx==1 && ctr_q==$past(ctr_q)+1));
  assert property (@(posedge clk) disable iff (rst)
    (state_q==STOP_BIT && ctr_q==END_VAL) |=> (state_q==IDLE && tx==1));

  // Data latch stability while busy
  assert property (@(posedge clk) disable iff (rst) (state_q!=IDLE) |-> $stable(data_q));

  // Ignore new_data while non-IDLE (no re-latch mid-frame)
  assert property (@(posedge clk) disable iff (rst)
    (state_q!=IDLE && new_data) |-> $stable(data_q));

  // State transition legality
  assert property (@(posedge clk) disable iff (rst)
    $rose(state_q==START_BIT) |-> $past(state_q)==IDLE);
  assert property (@(posedge clk) disable iff (rst)
    $rose(state_q==DATA) |-> ($past(state_q)==START_BIT || ($past(state_q)==DATA && $past(ctr_q)==END_VAL && $past(bit_ctr_q)!=3'd7)));
  assert property (@(posedge clk) disable iff (rst)
    $rose(state_q==STOP_BIT) |-> ($past(state_q)==DATA && $past(ctr_q)==END_VAL && $past(bit_ctr_q)==3'd7));
  assert property (@(posedge clk) disable iff (rst)
    $rose(state_q==IDLE) |-> ($past(state_q)==STOP_BIT && $past(ctr_q)==END_VAL));

  // Coverage

  // 1) Full frame from acceptance to idle
  cover property (@(posedge clk) disable iff (rst)
    accept ##1 (state_q==START_BIT, tx==0, ctr_q==0)
    ##1 (state_q==DATA && bit_ctr_q==0 && tx==data_q[0])
    ##[1:$] (state_q==DATA && bit_ctr_q==7 && ctr_q==END_VAL)
    ##1 (state_q==STOP_BIT && tx==1)
    ##[1:$] (state_q==IDLE));

  // 2) See both 0 and 1 data bits on tx during DATA
  cover property (@(posedge clk) disable iff (rst) (state_q==DATA && tx==1));
  cover property (@(posedge clk) disable iff (rst) (state_q==DATA && tx==0));

  // 3) Blocked idle
  cover property (@(posedge clk) disable iff (rst) (state_q==IDLE && block_q && busy && tx));

  // 4) new_data while busy (ignored)
  cover property (@(posedge clk) disable iff (rst) (state_q!=IDLE && new_data));

endmodule

// Bind into DUT
bind serial_tx serial_tx_sva #(.CLK_PER_BIT(CLK_PER_BIT), .CTR_SIZE(CTR_SIZE)) serial_tx_sva_i (
  .clk(clk),
  .rst(rst),
  .tx(tx),
  .busy(busy),
  .block(block),
  .data(data),
  .new_data(new_data),
  .ctr_q(ctr_q),
  .bit_ctr_q(bit_ctr_q),
  .data_q(data_q),
  .state_q(state_q),
  .block_q(block_q)
);