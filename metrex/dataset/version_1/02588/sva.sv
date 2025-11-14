// SVA for serial_tx
// Bind into DUT to access internals
module serial_tx_sva #(
  parameter int CLK_PER_BIT = 50
) (
  input  logic                clk,
  input  logic                rst,
  input  logic                tx,
  input  logic                busy,
  input  logic                block,
  input  logic                new_data,
  input  logic [7:0]          data,
  // internals (from DUT)
  input  logic [1:0]          state_q,
  input  logic [$clog2(CLK_PER_BIT)-1:0] ctr_q,
  input  logic [2:0]          bit_ctr_q,
  input  logic [7:0]          data_q,
  input  logic                busy_q,
  input  logic                block_q
);

  localparam int IDLE     = 2'd0;
  localparam int START_BIT= 2'd1;
  localparam int DATA     = 2'd2;
  localparam int STOP_BIT = 2'd3;

  default clocking cb @(posedge clk); endclocking
  // Synchronous reset in DUT; disable checks when rst asserted on sampling edge
  `define DISABLE_RST disable iff (rst)

  // Sanity: registered block matches past(block)
  assert property (`DISABLE_RST (block_q == $past(block)));

  // Busy semantics
  assert property (`DISABLE_RST (state_q==IDLE) |-> (busy==block_q));
  assert property (`DISABLE_RST (state_q!=IDLE) |-> busy);

  // TX mapping per state
  assert property (`DISABLE_RST (state_q==IDLE)     |-> tx==1'b1);
  assert property (`DISABLE_RST (state_q==START_BIT)|-> tx==1'b0);
  assert property (`DISABLE_RST (state_q==DATA)     |-> tx==data_q[bit_ctr_q]);
  assert property (`DISABLE_RST (state_q==STOP_BIT) |-> tx==1'b1);

  // Accept when idle and not blocked
  sequence accept_s;
    (state_q==IDLE && !block_q && new_data);
  endsequence
  // On accept: next state START_BIT, busy asserted, data latched
  assert property (`DISABLE_RST accept_s |=> (state_q==START_BIT && busy && data_q==$past(data)));

  // When blocked in IDLE, remain IDLE regardless of new_data
  assert property (`DISABLE_RST (state_q==IDLE && block_q) |=> state_q==IDLE);

  // Counter behavior in START_BIT/DATA/STOP_BIT
  // Increment while not at terminal
  assert property (`DISABLE_RST (state_q==START_BIT && ctr_q!=CLK_PER_BIT-1) |=> (state_q==START_BIT && ctr_q==$past(ctr_q)+1));
  assert property (`DISABLE_RST (state_q==DATA      && ctr_q!=CLK_PER_BIT-1) |=> (state_q==DATA      && ctr_q==$past(ctr_q)+1));
  assert property (`DISABLE_RST (state_q==STOP_BIT  && ctr_q!=CLK_PER_BIT-1) |=> (state_q==STOP_BIT  && ctr_q==$past(ctr_q)+1));

  // Terminal count transitions
  assert property (`DISABLE_RST (state_q==START_BIT && ctr_q==CLK_PER_BIT-1) |=> (state_q==DATA && ctr_q==0));
  assert property (`DISABLE_RST (state_q==DATA && ctr_q==CLK_PER_BIT-1 && bit_ctr_q!=3'd7) |=> (state_q==DATA && ctr_q==0 && bit_ctr_q==$past(bit_ctr_q)+1));
  assert property (`DISABLE_RST (state_q==DATA && ctr_q==CLK_PER_BIT-1 && bit_ctr_q==3'd7) |=> (state_q==STOP_BIT && ctr_q==0));
  // In STOP_BIT on terminal, go to IDLE (ctr next value is don't-care in DUT)
  assert property (`DISABLE_RST (state_q==STOP_BIT && ctr_q==CLK_PER_BIT-1) |=> (state_q==IDLE));

  // Data register stable during transmission (non-IDLE)
  assert property (`DISABLE_RST (state_q!=IDLE) |-> $stable(data_q));

  // After remaining in IDLE unblocked for at least 1 cycle, counters are cleared
  assert property (`DISABLE_RST (state_q==IDLE && !block_q && $past(state_q==IDLE && !block_q)) |-> (ctr_q==0 && bit_ctr_q==0));

  // TX only changes at frame start or bit boundaries
  assert property (`DISABLE_RST $changed(tx) |-> ($past(state_q)==IDLE || $past(ctr_q)==CLK_PER_BIT-1));

  // No X on outputs
  assert property (`DISABLE_RST !$isunknown({tx,busy}));

  // State-transition legality
  assert property (`DISABLE_RST (state_q==IDLE) |=> (state_q==IDLE || state_q==START_BIT));
  assert property (`DISABLE_RST (state_q==START_BIT) |=> (state_q==START_BIT || state_q==DATA));
  assert property (`DISABLE_RST (state_q==DATA) |=> (state_q==DATA || state_q==STOP_BIT));
  assert property (`DISABLE_RST (state_q==STOP_BIT) |=> (state_q==STOP_BIT || state_q==IDLE));

  // Coverage
  // Full frame: accept -> STOP_BIT terminal -> IDLE
  cover property (`DISABLE_RST accept_s ##[1:$] (state_q==STOP_BIT && ctr_q==CLK_PER_BIT-1) ##1 (state_q==IDLE && !block_q && !new_data));
  // See both 0 and 1 data levels during DATA
  cover property (`DISABLE_RST state_q==DATA && tx==1'b0);
  cover property (`DISABLE_RST state_q==DATA && tx==1'b1);
  // Blocked while new_data arrives in IDLE (ignored)
  cover property (`DISABLE_RST (state_q==IDLE && block_q && new_data) ##1 (state_q==IDLE));

endmodule

// Bind into DUT
bind serial_tx serial_tx_sva #(.CLK_PER_BIT(CLK_PER_BIT)) i_serial_tx_sva (
  .clk      (clk),
  .rst      (rst),
  .tx       (tx),
  .busy     (busy),
  .block    (block),
  .new_data (new_data),
  .data     (data),
  .state_q  (state_q),
  .ctr_q    (ctr_q),
  .bit_ctr_q(bit_ctr_q),
  .data_q   (data_q),
  .busy_q   (busy_q),
  .block_q  (block_q)
);