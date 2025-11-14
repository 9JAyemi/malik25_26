// SVA for synchronous_ram
// Place inside the module or bind to it. Focused, high-quality checks and coverage.
`ifdef SVA

default clocking cb @(posedge clock); endclocking

// Make $past safe
logic sva_init;
always @(posedge clock) sva_init <= 1'b1;

// Basic control integrity
assert property (cb disable iff(!sva_init) !$isunknown({clken,wren}));
assert property (cb disable iff(!sva_init) clken |-> (!$isunknown(address) && address < RAM_DEPTH));
assert property (cb disable iff(!sva_init) (clken && wren) |-> !$isunknown({byteena,data}));

// q behavior
// If clken was 1, q shows the previous-cycle value from that address (read-before-write semantics)
assert property (cb disable iff(!sva_init)
  $past(clken) |-> (q == $past(ram[$past(address)]))
);
// If clken was 0, q holds
assert property (cb disable iff(!sva_init)
  !$past(clken) |-> (q == $past(q))
);

// Write semantics (byte enables)
assert property (cb disable iff(!sva_init)
  ($past(clken && wren) && ($past(address) < RAM_DEPTH)) |-> (
    ram[$past(address)][7:0]  == ($past(byteena[0]) ? $past(data[7:0])   : $past(ram[$past(address)][7:0]))  &&
    ram[$past(address)][15:8] == ($past(byteena[1]) ? $past(data[15:8])  : $past(ram[$past(address)][15:8]))
  )
);

// No write when wren==0
assert property (cb disable iff(!sva_init)
  ($past(clken) && !$past(wren) && ($past(address) < RAM_DEPTH)) |-> (ram[$past(address)] == $past(ram[$past(address)]))
);

// No memory changes when clken==0
genvar gi;
generate
  for (gi=0; gi<RAM_DEPTH; gi++) begin: g_stable_no_clk_en
    assert property (cb disable iff(!sva_init) !$past(clken) |-> (ram[gi] == $past(ram[gi])));
  end
endgenerate

// Only the targeted address may change on a write
generate
  for (gi=0; gi<RAM_DEPTH; gi++) begin: g_only_target_changes
    assert property (cb disable iff(!sva_init)
      $past(clken && wren) |-> ((gi == $past(address)) || (ram[gi] == $past(ram[gi])))
    );
  end
endgenerate

// Coverage
cover property (cb disable iff(!sva_init) clken && !wren);                    // read
cover property (cb disable iff(!sva_init) clken && wren && byteena==2'b01);   // low byte write
cover property (cb disable iff(!sva_init) clken && wren && byteena==2'b10);   // high byte write
cover property (cb disable iff(!sva_init) clken && wren && byteena==2'b11);   // full word write
cover property (cb disable iff(!sva_init) clken && (address==0));
cover property (cb disable iff(!sva_init) clken && (address==(RAM_DEPTH-1)));
cover property (cb disable iff(!sva_init)
  $past(clken && wren && ($past(address) < RAM_DEPTH)) &&
  (q == $past(ram[$past(address)]))                                           // observe read-before-write on q
);

`endif