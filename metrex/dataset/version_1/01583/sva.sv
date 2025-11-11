// SVA checker for regfile. Bind this to the DUT.
// Focused, high-signal-value checks and compact coverage.

module regfile_sva (
  input logic         clk,
  input logic [2:0]   rd_at,
  input logic [2:0]   wr_at,
  input logic         wr_en,
  input logic [31:0]  din,
  input logic [31:0]  dout
);
  default clocking cb @(posedge clk); endclocking
  localparam int N = 3;

  // 1) Address range checks
  ap_rd_range: assert property (rd_at < N)
    else $error("regfile: rd_at out of range %0d", rd_at);
  ap_wr_range: assert property (!wr_en || (wr_at < N))
    else $error("regfile: wr_at out of range %0d on write", wr_at);

  // 2) Write correctness: next-cycle data at address equals prior din
  ap_write_effect: assert property (wr_en && (wr_at < N) |=> data[$past(wr_at)] == $past(din))
    else $error("regfile: write effect mismatch at addr %0d", $past(wr_at));

  // 3) Only the selected entry may change on a write
  genvar i;
  generate for (i=0;i<N;i++) begin : g_only_sel_changes
    ap_no_change_other_i: assert property (wr_en && $past(wr_at) < N && $past(wr_at) != i
                                           |=> data[i] == $past(data[i]))
      else $error("regfile: unexpected change at addr %0d", i);
  end endgenerate

  // 4) No write -> all entries hold
  ap_hold_no_write: assert property (!wr_en |=> (data[0] == $past(data[0]) &&
                                                 data[1] == $past(data[1]) &&
                                                 data[2] == $past(data[2])))
    else $error("regfile: data changed without write");

  // 5) Read correctness (combinational select)
  ap_read_correct: assert property (rd_at < N |-> dout == data[rd_at])
    else $error("regfile: dout mismatch vs data[rd_at]");

  // 6) DOUT only changes when address changes or that entry was written
  ap_dout_stability: assert property ($stable(rd_at) && ($past(rd_at) < N) &&
                                      !(wr_en && (wr_at < N) && (wr_at == $past(rd_at)))
                                      |=> $stable(dout))
    else $error("regfile: dout changed without cause");

  // 7) Knownness on valid operations
  ap_no_x_on_write: assert property (wr_en && (wr_at < N) && !$isunknown(din)
                                     |=> !$isunknown(data[$past(wr_at)]))
    else $error("regfile: X/Z written or stored");
  ap_no_x_on_read:  assert property ((rd_at < N) |-> !$isunknown(dout))
    else $error("regfile: X/Z on dout for valid rd_at");

  // Compact functional coverage
  cover property (wr_en && wr_at==0);
  cover property (wr_en && wr_at==1);
  cover property (wr_en && wr_at==2);
  cover property (rd_at==0);
  cover property (rd_at==1);
  cover property (rd_at==2);
  // Read-after-write to same address (next cycle)
  cover property (wr_en && (wr_at < N) ##1 (rd_at == $past(wr_at)));
  // Back-to-back writes to different addresses
  cover property (wr_en ##1 wr_en && ($past(wr_at) < N) && (wr_at < N) && (wr_at != $past(wr_at)));
endmodule

// Bind into the DUT (place in a separate sva file or a package included by the testbench)
bind regfile regfile_sva u_regfile_sva (.*);