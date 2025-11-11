// SVA for module tx
// Bind into DUT to access internal state, txpos, txdata_sampled
module tx_sva (
  input logic        clk,
  input logic        reset_,
  input logic        baud,
  input logic [7:0]  txdata,
  input logic        tx_enable,
  input logic        tx_ready,
  input logic        tx,
  input logic [1:0]  state,
  input logic [2:0]  txpos,
  input logic [7:0]  txdata_sampled
);
  localparam ST_IDLE    = 2'd0;
  localparam ST_TXSTART = 2'd1;
  localparam ST_TXDATA  = 2'd2;
  localparam ST_TXSTOP  = 2'd3;

  default clocking cb @(posedge clk); endclocking
  default disable iff (!reset_);

  // Invariants and reset
  assert property (state inside {ST_IDLE,ST_TXSTART,ST_TXDATA,ST_TXSTOP});
  assert property (tx_ready == (state == ST_IDLE));
  assert property (!reset_ |-> state==ST_IDLE && tx==1'b1 && txpos==3'd0 && txdata_sampled==8'h00);
  assert property ((state==ST_IDLE) |-> tx==1'b1);
  assert property (txpos inside {[3'd0:3'd7]});
  assert property ((state==ST_IDLE) |-> txpos==3'd0);
  assert property ((state!=ST_IDLE) |-> $stable(txdata_sampled));

  // State progress and gating
  assert property ((state==ST_IDLE && !tx_enable) |=> state==ST_IDLE);
  assert property ((state==ST_IDLE && tx_enable)  |=> state==ST_TXSTART);
  assert property ((state!=ST_IDLE && !baud) |-> $stable(state) && $stable(tx) && $stable(txpos));

  // TXSTART behavior
  assert property ((state==ST_TXSTART && baud) |-> tx==1'b0);
  assert property ((state==ST_TXSTART && baud) |=> state==ST_TXDATA);

  // TXDATA behavior
  assert property ((state==ST_TXDATA && baud) |-> tx==txdata_sampled[txpos]);
  assert property ((state==ST_TXDATA && baud && txpos!=3'd7) |=> state==ST_TXDATA && txpos==$past(txpos)+3'd1);
  assert property ((state==ST_TXDATA && baud && txpos==3'd7) |=> state==ST_TXSTOP && txpos==3'd0);

  // TXSTOP behavior
  assert property ((state==ST_TXSTOP && baud) |-> tx==1'b1);
  assert property ((state==ST_TXSTOP && baud) |=> state==ST_IDLE);

  // tx changes only on baud (outside reset)
  assert property ($changed(tx) |-> baud && (state!=ST_IDLE));

  // Sampling correctness
  assert property ((tx_enable && state==ST_IDLE) |=> txdata_sampled == $past(txdata));

  // Functional frame cover: start, 8 data bits LSB-first, stop, back to idle
  property p_full_frame;
    logic [7:0] d;
    (state==ST_IDLE && tx_enable, d=txdata)
    |=> ##[0:$] (state==ST_TXSTART && baud && tx==1'b0)
        ##[1:$] (state==ST_TXDATA && baud && tx==d[0])
        ##[1:$] (state==ST_TXDATA && baud && tx==d[1])
        ##[1:$] (state==ST_TXDATA && baud && tx==d[2])
        ##[1:$] (state==ST_TXDATA && baud && tx==d[3])
        ##[1:$] (state==ST_TXDATA && baud && tx==d[4])
        ##[1:$] (state==ST_TXDATA && baud && tx==d[5])
        ##[1:$] (state==ST_TXDATA && baud && tx==d[6])
        ##[1:$] (state==ST_TXDATA && baud && tx==d[7])
        ##[1:$] (state==ST_TXSTOP && baud && tx==1'b1)
        ##[1:$] (state==ST_IDLE);
  endproperty
  cover property (p_full_frame);

  // Cover back-to-back frames (any gap)
  cover property (p_full_frame ##[0:$] p_full_frame);

endmodule

bind tx tx_sva tx_sva_b (
  .clk(clk),
  .reset_(reset_),
  .baud(baud),
  .txdata(txdata),
  .tx_enable(tx_enable),
  .tx_ready(tx_ready),
  .tx(tx),
  .state(state),
  .txpos(txpos),
  .txdata_sampled(txdata_sampled)
);