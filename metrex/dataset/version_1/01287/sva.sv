// SVA for generic_dpram
// Bind this file alongside the DUT

module generic_dpram_sva #(parameter int aw=5, dw=16) ();

  // Basic input sanity (no X/Z on key controls/addrs at their clock edges)
  assert property (@(posedge rclk) !$isunknown({rce, oe, raddr}));
  assert property (@(posedge wclk) !$isunknown({wce, we, waddr, di}));

`ifdef VENDOR_FPGA
  // Read-address register behavior
  // Capture on enable
  assert property (@(posedge rclk) rce |-> ##0 (ra == raddr));
  // Hold when disabled
  assert property (@(posedge rclk) !rce |-> $stable(ra));

  // DO must always reflect mem[ra] (check on both domains and after NBA)
  assert property (@(posedge rclk or posedge wclk) 1 |-> ##0 (do == mem[ra]));

  // oe has no effect in this implementation
  assert property (@(posedge rclk or posedge wclk) $changed(oe) |-> ##0 (do == mem[ra]));

  // Write-port behavior
  // On a qualified write, memory updates to di at the same tick (NBA) at wclk
  assert property (@(posedge wclk) (we && wce) |-> ##0 (mem[waddr] == di));

  // When not writing, the currently addressed location must not change at next wclk
  // (samples the address, then ensures that location is stable across the cycle)
  property p_no_write_keeps_addr;
    logic [aw-1:0] a;
    @(posedge wclk) (1, a = waddr, !(we && wce)) |=> (mem[a] == $past(mem[a]));
  endproperty
  assert property (p_no_write_keeps_addr);

  // -------------- Coverage --------------
  // Exercise write and read enables
  cover property (@(posedge wclk) we && wce);
  cover property (@(posedge rclk) rce);

  // Write followed by a read of the same address at some later time
  // (cross-clock RAW scenario)
  sequence w_then_r_same_addr;
    logic [aw-1:0] a; logic [dw-1:0] d;
    @(posedge wclk) (we && wce, a = waddr, d = di)
    ##[1:$] @(posedge rclk) (ra == a && do == mem[a]);
  endsequence
  cover property (w_then_r_same_addr);

  // Two writes to the same address at different times
  sequence waw_same_addr;
    logic [aw-1:0] a;
    @(posedge wclk) (we && wce, a = waddr)
    ##[1:$] (we && wce && waddr == a);
  endsequence
  cover property (waw_same_addr);
`else
  // Generic checks when internal mem/ra may not exist
  assert property (@(posedge rclk) !rce |-> $stable(raddr));
  cover  property (@(posedge wclk) we && wce);
  cover  property (@(posedge rclk) rce);
`endif

endmodule

bind generic_dpram generic_dpram_sva #(.aw(aw), .dw(dw)) u_generic_dpram_sva();