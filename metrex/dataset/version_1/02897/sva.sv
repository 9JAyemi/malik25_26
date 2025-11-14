// Assertions and coverage for sequencer
// Non-intrusive bind; focuses on protocol, state, counters, and datapath

module sequencer_sva
  #(parameter RPIPE=2, ABITS=16, DBITS=64, SBITS=16, CBITS=24)
  (input clock, reset,
   input fpc_read, fpc_valid,
   input [63:0] fpc_data,
   input tpc_ready, tpc_write,
   input [63:0] tpc_data,
   input rvalid, wvalid,
   input [ABITS-1:0] address,
   input [DBITS-1:0] wdata, rdata,
   input [SBITS-1:0] status,
   input [1:0] state,
   input inc,
   input [CBITS-1:0] count);

  default clocking cb @(posedge clock); endclocking

  // Combinational equivalences
  assert property (fpc_read == (fpc_valid && (state inside {2'd0,2'd2})));
  assert property (tpc_data == rdata);

  // Registered outputs match next-state equations
  assert property (disable iff (reset) rvalid == $past(state==2'd3 && tpc_ready));
  assert property (disable iff (reset) wvalid == $past(state==2'd2 && fpc_read));
  assert property (disable iff (reset) !(rvalid && wvalid));

  // Address behavior
  assert property (disable iff (reset) $past(state==2'd0) |-> address == $past(fpc_data[ABITS-1:0]));
  assert property (disable iff (reset)
                   $past(state!=2'd0 && inc && (rvalid || wvalid))
                   |-> address == $past(address)+1);
  assert property (disable iff (reset)
                   $past(state!=2'd0 && !(inc && (rvalid || wvalid)))
                   |-> address == $past(address));

  // inc latch behavior
  assert property (disable iff (reset) $past(state==2'd0) |-> inc == $past(fpc_data[61]));
  assert property (disable iff (reset) $past(state!=2'd0) |-> inc == $past(inc));

  // wdata follows fpc_data
  assert property (disable iff (reset) wdata == $past(fpc_data[DBITS-1:0]));

  // count behavior per state
  assert property (disable iff (reset) $past(state==2'd0) |-> count == $past(fpc_data[CBITS+31:32]));
  assert property (disable iff (reset) $past(state==2'd1) |-> count == $past(count) - 1);
  assert property (disable iff (reset) $past(state==2'd2) |-> count == $past(count) - ($past(state==2'd2 && fpc_read) ? 1:0));
  assert property (disable iff (reset) $past(state==2'd3) |-> count == $past(count) - ($past(state==2'd3 && tpc_ready) ? 1:0));

  // State transitions and range
  assert property (state inside {2'd0,2'd1,2'd2,2'd3});
  assert property (reset |=> state==2'd0);
  assert property (disable iff (reset)
                   $past(state==2'd0) |-> state == ($past(fpc_read) ? $past(fpc_data[63:62]) : 2'd0));
  assert property (disable iff (reset)
                   $past(state inside {2'd1,2'd2,2'd3})
                   |-> state == (($past(count[CBITS-1:1])==0) ? 2'd0 : $past(state)));

  // tpc_write is rvalid delayed by RPIPE
  assert property (tpc_write == $past(rvalid, RPIPE));

  // Handshake implications
  assert property (disable iff (reset) rvalid |-> $past(state==2'd3 && tpc_ready));
  assert property (disable iff (reset) wvalid |-> $past(state==2'd2 && fpc_read));

  // Coverage
  cover property (disable iff (reset) (state==2'd0 && fpc_read && fpc_data[63:62]==2'd1) ##1 state==2'd1);
  cover property (disable iff (reset) (state==2'd0 && fpc_read && fpc_data[63:62]==2'd2) ##1 state==2'd2);
  cover property (disable iff (reset) (state==2'd0 && fpc_read && fpc_data[63:62]==2'd3) ##1 state==2'd3);
  cover property (disable iff (reset) (state==2'd2 && inc && fpc_valid) ##1 (wvalid && address==$past(address)+1));
  cover property (disable iff (reset) (state==2'd3 && inc && tpc_ready) ##1 (rvalid && address==$past(address)+1));
  cover property (disable iff (reset) (state inside {2'd1,2'd2,2'd3} && count[CBITS-1:1]==0) ##1 state==2'd0);
  cover property (rvalid ##[RPIPE] tpc_write);

endmodule

bind sequencer sequencer_sva #(.RPIPE(RPIPE), .ABITS(ABITS), .DBITS(DBITS), .SBITS(SBITS), .CBITS(CBITS)) i_sequencer_sva
(
  .clock(clock), .reset(reset),
  .fpc_read(fpc_read), .fpc_valid(fpc_valid), .fpc_data(fpc_data),
  .tpc_ready(tpc_ready), .tpc_write(tpc_write), .tpc_data(tpc_data),
  .rvalid(rvalid), .wvalid(wvalid),
  .address(address), .wdata(wdata), .rdata(rdata),
  .status(status), .state(state), .inc(inc), .count(count)
);

// Assertions for delay_n
module delay_n_sva #(parameter N=2) (input clock, in, out);
  default clocking cb @(posedge clock); endclocking
  assert property (out == $past(in, N));
  cover  property (in ##[N] out);
endmodule

bind delay_n delay_n_sva #(.N(N)) i_delay_n_sva (.clock(clock), .in(in), .out(out));