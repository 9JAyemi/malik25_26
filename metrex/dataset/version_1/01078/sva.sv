// Bind these SVA into the DUT scope
bind block_memory_generator block_memory_generator_sva bmgen_sva();

module block_memory_generator_sva;

  // Write updates targeted location with current dina (handle NBA with ##0)
  property p_write_updates_target;
    @(posedge clka) ENA |-> ##0 (mem[addra] == $past(dina,0));
  endproperty
  assert property (p_write_updates_target);

  // No write when disabled (targeted location holds)
  property p_write_hold_when_disabled;
    @(posedge clka) !ENA |-> ##0 $stable(mem[addra]);
  endproperty
  assert property (p_write_hold_when_disabled);

  // Read transfers mem to DOUTB when enabled (handle NBA with ##0)
  property p_read_loads_from_mem;
    @(posedge clkb) ENB |-> ##0 (DOUTB == $past(mem[addrb],0));
  endproperty
  assert property (p_read_loads_from_mem);

  // DOUTB holds when read disabled
  property p_read_hold_when_disabled;
    @(posedge clkb) !ENB |-> ##0 $stable(DOUTB);
  endproperty
  assert property (p_read_hold_when_disabled);

  // DOUTB can change only on clkb and only when ENB
  property p_doutb_changes_only_on_clkb;
    $changed(DOUTB) |-> ($rose(clkb) && ENB);
  endproperty
  assert property (p_doutb_changes_only_on_clkb);

  // Controls/addr/data known at sampling edges
  property p_write_ctrl_known;
    @(posedge clka) !$isunknown(ENA) and (ENA |-> (!$isunknown(addra) && !$isunknown(dina)));
  endproperty
  assert property (p_write_ctrl_known);

  property p_read_ctrl_known;
    @(posedge clkb) !$isunknown(ENB) and (ENB |-> !$isunknown(addrb));
  endproperty
  assert property (p_read_ctrl_known);

  // Coverage: basic ops and key scenarios
  cover property (@(posedge clka) ENA);
  cover property (@(posedge clkb) ENB);
  cover property (@(posedge clka) ENA ##1 ENA);   // back-to-back writes
  cover property (@(posedge clkb) ENB ##1 ENB);   // back-to-back reads

  // Write on A then (eventually) read same address on B
  property c_write_then_read_same_addr;
    logic [9:0] a;
    @(posedge clka) ENA && (a = addra) |-> ##[1:$] ($rose(clkb) && ENB && (addrb == a));
  endproperty
  cover property (c_write_then_read_same_addr);

  // Same-cycle write/read collision to same address (for visibility)
  cover property ($rose(clka) && ENA && $rose(clkb) && ENB && (addra == addrb));

endmodule