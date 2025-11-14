// SVA checker for icache_tag_ram
// Focus: functional correctness of 1-cycle registered read with read-before-write semantics,
// data visibility after writes, stability when not written, and basic X-safety.

module icache_tag_ram_sva
  #(parameter AW = 8, DW = 20)
  (
    input              clk_i,
    input              rst_i,
    input  [AW-1:0]    addr_i,
    input  [DW-1:0]    data_i,
    input              wr_i,
    input  [DW-1:0]    data_o
  );

  // Past-valid trackers
  logic past1, past2;
  always_ff @(posedge clk_i) begin
    if (rst_i) begin
      past1 <= 1'b0;
      past2 <= 1'b0;
    end else begin
      past2 <= past1;
      past1 <= 1'b1;
    end
  end

  // Basic X-safety on controls (concise but high-value)
  // wr_i must be known; if writing, addr_i and data_i must be known
  assert property (@(posedge clk_i) !$isunknown(wr_i))
    else $error("wr_i unknown at clk edge");
  assert property (@(posedge clk_i) disable iff (rst_i)
                   wr_i |-> !$isunknown({addr_i, data_i}))
    else $error("addr_i/data_i unknown while wr_i=1");

  // Core functional properties (read-before-write, 1-cycle registered read)

  // 1) If address is held and there was no write last cycle, output is stable
  assert property (@(posedge clk_i) disable iff (!past1 || rst_i)
                   (addr_i == $past(addr_i) && !$past(wr_i)) |-> (data_o == $past(data_o)))
    else $error("Data changed without a write to held address");

  // 2) If address is held and there was a write last cycle, output shows last cycle's write data
  assert property (@(posedge clk_i) disable iff (!past1 || rst_i)
                   (addr_i == $past(addr_i) && $past(wr_i)) |-> (data_o == $past(data_i)))
    else $error("Newly written data not observed on next-cycle read of same address");

  // 3) Back-to-back writes to same address: most recent write wins
  // If two consecutive writes to same addr, and we keep that addr a 3rd cycle,
  // the read returns the 2nd write's data.
  assert property (@(posedge clk_i) disable iff (!past2 || rst_i)
                   ($past(wr_i,2) && $past(wr_i,1) &&
                    ($past(addr_i,2) == $past(addr_i,1)) &&
                    (addr_i == $past(addr_i,1)))
                   |-> (data_o == $past(data_i,1)))
    else $error("Back-to-back write precedence violated");

  // 4) When holding address (regardless of write), output must be known
  assert property (@(posedge clk_i) disable iff (!past1 || rst_i)
                   (addr_i == $past(addr_i)) |-> (!$isunknown(data_o)))
    else $error("data_o unknown on held address");

  // Coverage: exercise key scenarios concisely
  cover property (@(posedge clk_i) $past(wr_i) && (addr_i == $past(addr_i)));           // write -> same addr read
  cover property (@(posedge clk_i) (addr_i == $past(addr_i)) && !$past(wr_i));           // held addr, no write
  cover property (@(posedge clk_i) $past(wr_i,2) && $past(wr_i,1) &&
                               ($past(addr_i,2) == $past(addr_i,1)) &&
                               (addr_i == $past(addr_i,1)));                            // two writes then read same addr

endmodule

// Bind into DUT
bind icache_tag_ram icache_tag_ram_sva #(.AW(8), .DW(20)) u_icache_tag_ram_sva (
  .clk_i  (clk_i),
  .rst_i  (rst_i),
  .addr_i (addr_i),
  .data_i (data_i),
  .wr_i   (wr_i),
  .data_o (data_o)
);