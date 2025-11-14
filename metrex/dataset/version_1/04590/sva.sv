// SVA for module tx
// Bind example (adjust instance name as needed):
// bind tx tx_sva u_tx_sva(.clk(clk), .reset_(reset_), .baud(baud), .txdata(txdata),
//                         .tx_enable(tx_enable), .tx_ready(tx_ready), .tx(tx),
//                         .state(state), .txpos(txpos), .txdata_sampled(txdata_sampled));

module tx_sva(
  input logic        clk,
  input logic        reset_,
  input logic        baud,
  input logic [7:0]  txdata,
  input logic        tx_enable,
  input logic        tx_ready,
  input logic        tx,
  // internal DUT signals (bind to these)
  input logic [1:0]  state,
  input logic [2:0]  txpos,
  input logic [7:0]  txdata_sampled
);
  localparam ST_IDLE    = 2'd0;
  localparam ST_TXSTART = 2'd1;
  localparam ST_TXDATA  = 2'd2;
  localparam ST_TXSTOP  = 2'd3;

  default clocking cb @ (posedge clk); endclocking
  default disable iff (!reset_);

  // Reset values
  assert property (!reset_ |-> (state==ST_IDLE && tx==1'b1 && txpos==3'd0 && txdata_sampled==8'h00));

  // tx_ready correctness
  assert property (tx_ready == (state==ST_IDLE));

  // State transitions and holds
  assert property ((state==ST_IDLE  &&  tx_enable)        |=> state==ST_TXSTART);
  assert property ((state==ST_TXSTART && !baud)           |=> state==ST_TXSTART);
  assert property ((state==ST_TXSTART &&  baud)           |=> state==ST_TXDATA);

  assert property ((state==ST_TXDATA && (!baud || txpos!=3'd7)) |=> state==ST_TXDATA);
  assert property ((state==ST_TXDATA &&  baud && txpos==3'd7)   |=> state==ST_TXSTOP);

  assert property ((state==ST_TXSTOP && !baud)            |=> state==ST_TXSTOP);
  assert property ((state==ST_TXSTOP &&  baud)            |=> state==ST_IDLE);

  // tx behavior
  assert property (state==ST_IDLE |-> tx==1'b1);
  assert property ((state==ST_TXSTART && baud) |-> tx==1'b0);
  assert property ((state==ST_TXDATA  && baud) |-> tx==txdata_sampled[txpos]);
  assert property ((state==ST_TXSTOP  && baud) |-> tx==1'b1);

  // tx changes only on baud-qualified TX states
  assert property (!((state==ST_TXSTART && baud) || (state==ST_TXDATA && baud) || (state==ST_TXSTOP && baud)) |-> $stable(tx));

  // txpos behavior
  assert property (state==ST_IDLE |-> txpos==3'd0);
  assert property ((state==ST_TXDATA &&  baud) |=> txpos == $past(txpos)+3'd1);
  assert property ((state==ST_TXDATA && !baud) |=> txpos == $past(txpos));
  assert property ((state inside {ST_TXSTART,ST_TXSTOP}) |=> txpos == $past(txpos));
  // First data bit index must start at 0 on entry to TXDATA from START+baud
  assert property ($past(state)==ST_TXSTART && $past(baud) && state==ST_TXDATA |-> txpos==3'd0);

  // txdata_sampled capture/hold
  assert property ($changed(txdata_sampled) |-> $past(tx_ready && tx_enable));
  assert property ((tx_ready && tx_enable)  |=> txdata_sampled == $past(txdata));
  assert property ((!tx_ready) |-> $stable(txdata_sampled));

  // Coverage
  cover property ((state==ST_IDLE && tx_enable)
                  ##1 state==ST_TXSTART
                  ##[1:$] (state==ST_TXSTART && baud && tx==1'b0)
                  ##1 state==ST_TXDATA
                  ##[1:$] (state==ST_TXDATA && baud && txpos==3'd0)
                  ##[1:$] (state==ST_TXDATA && baud && txpos==3'd7)
                  ##[1:$] (state==ST_TXSTOP && baud && tx==1'b1)
                  ##1 state==ST_IDLE);

  // Cover each transition at least once
  cover property (state==ST_IDLE     && tx_enable ##1 state==ST_TXSTART);
  cover property (state==ST_TXSTART  && baud      ##1 state==ST_TXDATA);
  cover property (state==ST_TXDATA   && baud && txpos==3'd7 ##1 state==ST_TXSTOP);
  cover property (state==ST_TXSTOP   && baud      ##1 state==ST_IDLE);

  // Back-to-back frame cover (no idle gap beyond required)
  cover property ((state==ST_TXSTOP && baud)
                  ##1 (state==ST_IDLE && tx_enable)
                  ##1 state==ST_TXSTART);

endmodule