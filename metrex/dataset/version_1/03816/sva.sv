// SVA checker for regfile
// Bind this checker without modifying the DUT
module regfile_sva
(
  input  logic         clk,
  input  logic         nrst,
  input  logic         wr,
  input  logic [4:0]   raddr1, raddr2, waddr,
  input  logic [31:0]  din,
  input  logic [31:0]  dout1, dout2,
  input  logic [31:0]  ram1, ram2, ram3,
  ref    logic [31:0]  ram [0:31]
);

  // Basic knownness
  assert property (@(posedge clk) disable iff (!nrst)
    !wr or !$isunknown({waddr,din})
  );

  assert property (@(negedge clk) disable iff (!nrst)
    !$isunknown({raddr1,raddr2})
  );

  // Writes update memory at the same posedge
  assert property (@(posedge clk) disable iff (!nrst)
    wr |-> (ram[waddr] == din)
  );

  // No write -> currently addressed location is stable across posedges
  assert property (@(posedge clk) disable iff (!nrst)
    !wr |-> $stable(ram[waddr])
  );

  // Read behavior at negedge (including hardwired zero register)
  assert property (@(negedge clk) disable iff (!nrst)
    dout1 == ((raddr1 == 5'd0) ? 32'd0 : ram[raddr1])
  );

  assert property (@(negedge clk) disable iff (!nrst)
    dout2 == ((raddr2 == 5'd0) ? 32'd0 : ram[raddr2])
  );

  // If both ports read same non-zero address, data must match
  assert property (@(negedge clk) disable iff (!nrst)
    (raddr1 == raddr2) && (raddr1 != 5'd0) |-> (dout1 == dout2)
  );

  // Cross-edge write->read forwarding (write at posedge, read at next negedge)
  assert property (@(negedge clk) disable iff (!nrst)
    $past(wr,1, posedge clk) && ($past(waddr,1, posedge clk) == raddr1) && (raddr1 != 5'd0)
      |-> (dout1 == $past(din,1, posedge clk))
  );

  assert property (@(negedge clk) disable iff (!nrst)
    $past(wr,1, posedge clk) && ($past(waddr,1, posedge clk) == raddr2) && (raddr2 != 5'd0)
      |-> (dout2 == $past(din,1, posedge clk))
  );

  // Mirrored taps must equal array values
  assert property (@(posedge clk or negedge clk) disable iff (!nrst)
    (ram1 == ram[5'd1]) && (ram2 == ram[5'd2]) && (ram3 == ram[5'd3])
  );

  // Outputs known when updated
  assert property (@(negedge clk) disable iff (!nrst)
    !$isunknown({dout1,dout2})
  );

  // Coverage
  cover property (@(posedge clk) disable iff (!nrst) wr);
  cover property (@(negedge clk) disable iff (!nrst) (raddr1==5'd0) && (dout1==32'd0));
  cover property (@(negedge clk) disable iff (!nrst) (raddr1!=5'd0));
  cover property (@(negedge clk) disable iff (!nrst)
    $past(wr,1, posedge clk) && ($past(waddr,1, posedge clk)==raddr1) && (raddr1!=5'd0)
      && (dout1 == $past(din,1, posedge clk))
  );
  cover property (@(negedge clk) disable iff (!nrst)
    (raddr1==raddr2) && (raddr1!=5'd0) && (dout1==dout2)
  );

endmodule

// Bind to DUT (tool/SystemVerilog supports ref port to internal RAM)
bind regfile regfile_sva u_regfile_sva
(
  .clk   (clk),
  .nrst  (nrst),
  .wr    (wr),
  .raddr1(raddr1),
  .raddr2(raddr2),
  .waddr (waddr),
  .din   (din),
  .dout1 (dout1),
  .dout2 (dout2),
  .ram1  (ram1),
  .ram2  (ram2),
  .ram3  (ram3),
  .ram   (ram)
);