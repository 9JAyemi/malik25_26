// SVA checker for fifo
module fifo_sva
(
  input  logic         clk,
  input  logic         reset,
  input  logic [15:0]  in,
  input  logic [15:0]  out,
  input  logic         rd,
  input  logic         wr,
  input  logic         empty,
  input  logic         full,
  input  logic [11:0]  cnt,
  // internal DUT signals (bound hierarchically)
  input  logic [11:0]  in_ptr,
  input  logic [11:0]  out_ptr,
  input  logic         equal
);
  localparam int unsigned DEPTH = 2048;
  localparam int unsigned AW    = 11;   // address bits
  localparam int unsigned PW    = 12;   // pointer bits (AW+1)
  localparam int unsigned DW    = 16;

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Basic sanity: no X on status/cnt after reset deasserted; out only checked on valid read
  assert property (!$isunknown({empty,full,cnt})));

  // Reset behavior (allowing 1-cycle latency for flag computation)
  assert property (reset |=> (in_ptr==12'd0 && out_ptr==12'd0));
  assert property (reset |=> (empty && !full && cnt==12'd0));

  // Flag correctness and mutual exclusion
  assert property (equal == (in_ptr[AW-1:0] == out_ptr[AW-1:0]));
  assert property (empty <-> (in_ptr == out_ptr));
  assert property (full  <-> ( (in_ptr[AW-1:0]==out_ptr[AW-1:0]) && (in_ptr[PW-1]!=out_ptr[PW-1]) ));
  assert property (!(empty && full));

  // Count invariants
  assert property (cnt <= DEPTH);
  assert property ((equal && (in_ptr[PW-1]==out_ptr[PW-1])) |-> (cnt==12'd0));
  assert property ((equal && (in_ptr[PW-1]!=out_ptr[PW-1])) |-> (cnt==12'd2048));
  assert property ((!equal) |-> (cnt>12'd0 && cnt<12'd2048));

  // Pointer updates
  assert property (in_ptr == $past(in_ptr) + (wr ? 12'd1 : 12'd0));
  assert property (out_ptr == $past(out_ptr) + (rd ? 12'd1 : 12'd0));

  // Count updates (guarded by legal operations)
  assert property ((wr && !rd && !full)  |-> (cnt == $past(cnt)+12'd1));
  assert property ((rd && !wr && !empty) |-> (cnt == $past(cnt)-12'd1));
  assert property ((rd && wr && !empty && !full) |-> (cnt == $past(cnt)));

  // Usage safety (convert to assume if preferred for formal)
  assert property (!(wr && full));
  assert property (!(rd && empty));

  // Data integrity scoreboard (compact, cycle-accurate for this RTL)
  logic [DW-1:0] q[$];
  always_ff @(posedge clk) begin
    if (reset) begin
      q.delete();
    end else begin
      if (wr && !full) q.push_back(in);
      if (rd && !empty) begin
        assert (q.size()>0) else $error("FIFO underflow vs scoreboard");
        assert (out == q[0]) else $error("FIFO data mismatch: exp=%0h got=%0h", q[0], out);
        q.pop_front();
      end
      assert (q.size() == cnt) else $error("FIFO count mismatch: q=%0d cnt=%0d", q.size(), cnt);
    end
  end

  // Functional coverage (concise, key scenarios)
  cover property (!full ##[1:$] full);                   // reaches full
  cover property (full ##[1:$] empty);                   // drains to empty
  cover property ($rose(in_ptr[PW-1]));                  // write pointer wrap MSB toggle
  cover property ($rose(out_ptr[PW-1]));                 // read pointer wrap MSB toggle
  cover property (!empty && !full ##1 (rd && wr) ##1 (cnt == $past(cnt,1))); // simultaneous rd/wr mid-occupancy
endmodule

// Bind SVA to DUT (connect internal signals)
bind fifo fifo_sva i_fifo_sva (
  .clk    (clk),
  .reset  (reset),
  .in     (in),
  .out    (out),
  .rd     (rd),
  .wr     (wr),
  .empty  (empty),
  .full   (full),
  .cnt    (cnt),
  .in_ptr (in_ptr),
  .out_ptr(out_ptr),
  .equal  (equal)
);