// SVA for vga_palette_regs
module vga_palette_regs_sva;

  // Bound into vga_palette_regs; can directly reference clk, attr, index, address, write, read_data, write_data, palette

  logic past_valid;
  initial past_valid = 0;
  always @(posedge clk) past_valid <= 1'b1;

  default clocking cb @(posedge clk); endclocking

  // 1-cycle latency: outputs reflect array content sampled on previous cycle
  assert property (disable iff (!past_valid)
    index == $past(palette[$past(attr)])
  );

  assert property (disable iff (!past_valid)
    read_data == $past(palette[$past(address)])
  );

  // Write takes effect exactly on the next cycle at the addressed entry
  assert property (disable iff (!past_valid)
    $past(write) |-> (palette[$past(address)] == $past(write_data))
  );

  // Any change to an entry must be caused by a write to that entry in the previous cycle, and must match write_data
  genvar i;
  for (i = 0; i < 16; i++) begin : g_mem_change_checks
    assert property (disable iff (!past_valid)
      (palette[i] != $past(palette[i])) |-> ($past(write && (address == i)) && (palette[i] == $past(write_data)))
    );
  end

  // Coverage: exercise key scenarios
  //  - Same-cycle read-before-write hazard on index path (address == attr)
  cover property (write && (address == attr));

  //  - Write followed by readback on same address via read_data next cycle
  cover property (write ##1 (address == $past(address)) && (read_data == $past(write_data)));

  //  - Write followed by index picking up the new value next cycle when attr targets that address
  cover property (write ##1 (attr == $past(address)) && (index == $past(write_data)));

endmodule

bind vga_palette_regs vga_palette_regs_sva sva_vga_palette_regs();