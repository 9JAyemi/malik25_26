// SVA checker for sram
module sram_sva #(parameter AW=12, DW=16) (
  input  logic              clock,
  input  logic [DW-1:0]     data,
  input  logic [AW-1:0]     rdaddress,
  input  logic [AW-1:0]     wraddress,
  input  logic              wren,
  input  logic [DW-1:0]     q
);

  // Reference model
  logic [DW-1:0] ref_mem [0:(1<<AW)-1];
  bit            ref_valid [0:(1<<AW)-1];

  // Init and clocking
  logic init;
  initial begin
    init = 1'b0;
    foreach (ref_valid[i]) ref_valid[i] = 1'b0;
  end
  always @(posedge clock) init <= 1'b1;

  default clocking cb @(posedge clock); endclocking
  default disable iff (!init);

  // Update reference model on writes
  always @(posedge clock) begin
    if (wren) begin
      ref_mem[wraddress]  <= data;
      ref_valid[wraddress] <= 1'b1;
    end
  end

  // X-propagation checks
  assert property (!$isunknown(wren)) else $error("wren is X");
  assert property ( wren |-> !$isunknown({wraddress, data})) else $error("write addr/data X");
  assert property (!wren |-> !$isunknown(rdaddress)) else $error("read addr X");

  // q must not update on write cycles (registered read-only path)
  assert property (wren |=> q == $past(q)) else $error("q changed during write");

  // q changes only as a result of a read cycle in the previous tick
  assert property ($changed(q) |-> $past(!wren)) else $error("q changed without read");

  // Read returns the modeled memory value (1-cycle sampled check)
  assert property ((!wren && ref_valid[rdaddress]) |=> q == $past(ref_mem[rdaddress]))
    else $error("q mismatch vs model on read");

  // Read-after-write same address returns the just-written data (next cycle)
  assert property ( wren ##1 (!wren && rdaddress == $past(wraddress)) |-> q == $past(data))
    else $error("RAW mismatch");

  // Basic functional coverage
  cover property (wren);                               // observe writes
  cover property (!wren);                              // observe reads
  cover property (wren ##1 !wren && rdaddress == $past(wraddress)); // RAW same addr
  cover property (wren ##1 wren && wraddress != $past(wraddress));  // back-to-back writes
  cover property (!wren ##1 !wren && rdaddress != $past(rdaddress)); // back-to-back reads

endmodule

// Bind into DUT
bind sram sram_sva #(.AW(12), .DW(16))) sram_sva_i (
  .clock(clock),
  .data(data),
  .rdaddress(rdaddress),
  .wraddress(wraddress),
  .wren(wren),
  .q(q)
);