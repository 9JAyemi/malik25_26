// SVA checker for ahb_lite_memory_interface
module ahb_lite_memory_interface_sva;

  // Bound into DUT scope; can see DUT signals/locals (memory, etc.)
  default clocking cb @(posedge hclk); endclocking
  default disable iff (!hresetn)

  localparam IDLE   = 2'b00;
  localparam BUSY   = 2'b01;
  localparam NONSEQ = 2'b10;
  localparam SEQ    = 2'b11;

  // Basic protocol/handshake
  sequence hand; hsel && hready && (htrans inside {NONSEQ,SEQ}); endsequence

  // Reset values
  assert property (!hresetn |-> (hrdata==32'h0 && hready==1'b1 && hresp==2'b00));

  // Always-ready, OKAY response
  assert property (hready==1'b1);
  assert property (hresp==2'b00);

  // No BUSY transfer while selected
  assert property (!(hsel && hready && (htrans==BUSY)));

  // Word-only, aligned, in-range accesses
  assert property (hand |-> (hsize==3'b010) && (haddr[1:0]==2'b00));
  assert property (hand |-> (haddr[31:2] < 32'd256));

  // No X/Z on inputs during a valid transfer
  assert property (hand |-> !$isunknown({haddr,hwdata,hwrite,hsize,htrans,hsel}));

  // Write updates memory at the addressed location on the next cycle
  assert property ((hand && hwrite) |=> memory[$past(haddr[31:2])] == $past(hwdata));

  // Read returns the addressed memory word on the next cycle
  assert property ((hand && !hwrite) |=> hrdata == $past(memory[haddr[31:2]]));

  // hrdata changes only on read handshakes
  assert property (!(hand && !hwrite) |=> $stable(hrdata));

  // Read-after-write to same address returns the just-written data
  assert property ( (hand && hwrite) ##1 (hand && !hwrite && (haddr[31:2]==$past(haddr[31:2])))
                    |=> hrdata == $past(hwdata,1) );

  // Coverage
  cover property (hand && hwrite);
  cover property (hand && !hwrite);
  cover property (hand && hwrite && (haddr[31:2]==0));
  cover property (hand && !hwrite && (haddr[31:2]==0));
  cover property (hand && hwrite && (haddr[31:2]==32'd255));
  cover property (hand && !hwrite && (haddr[31:2]==32'd255));
  cover property ( (hand && hwrite) ##1 (hand && !hwrite && (haddr[31:2]==$past(haddr[31:2]))) );

endmodule

bind ahb_lite_memory_interface ahb_lite_memory_interface_sva sva_i();