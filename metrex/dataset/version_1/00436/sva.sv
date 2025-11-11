// SVA binders for top_module and submodules
// Focused, concise checks + key coverage

// Top-level checks: mux correctness, no X on key outputs, coverage of both paths
module sva_top (top_module dut);
  default clocking cb @(posedge dut.clk); endclocking
  bit init; always_ff @(posedge dut.clk) init <= 1'b1;

  // Mux correctness
  assert property (dut.read_data == (dut.select ? dut.func_data : dut.ram_data));

  // Outputs only 0 or F from isd; fm output legal
  assert property (dut.in_detect inside {4'h0, 4'hF});
  assert property ((dut.func_data == 4'h0) || (dut.func_data == dut.ram_data));

  // No X on critical externally visible signals after first cycle
  assert property (init |-> (!$isunknown({dut.select, dut.read_en, dut.write_en,
                                          dut.write_addr, dut.read_addr, dut.in,
                                          dut.read_data})) );

  // Coverage: exercise both mux legs
  cover property (dut.select == 1'b0);
  cover property (dut.select == 1'b1);

  // Coverage: end-to-end path when fm is selected and gate is open
  cover property (dut.select && (dut.in_detect==4'hF) && (dut.read_data==dut.ram_data));
endmodule

// dual_port_ram checks: reset/write semantics, async read behavior, read_en neutrality
module sva_dp_ram (dual_port_ram d);
  default clocking cb @(posedge d.clk); endclocking
  bit init; always_ff @(posedge d.clk) init <= 1'b1;

  // Combinational read matches memory at sampled address
  assert property (d.read_data == d.memory[d.read_addr]);

  // Write behavior (no reset): next cycle memory at written address == past data
  assert property (disable iff (d.reset || !init)
                   d.write_en |=> d.memory[$past(d.write_addr)] == $past(d.write_data));

  // Reset behavior: on a cycle with reset, that addressed location becomes 0xF
  assert property (disable iff (!init)
                   d.reset |=> d.memory[$past(d.write_addr)] == 4'hF);

  // read_en has no functional effect: toggling it does not change read_data
  // when address is stable and no write hits that address
  assert property (disable iff (!init || d.reset)
    ($stable(d.read_addr) && $changed(d.read_en) &&
     !( $past(d.write_en) && ($past(d.write_addr)==$past(d.read_addr)) ))
    |=> d.read_data == $past(d.read_data));

  // Coverage: write-then-read same address
  cover property (disable iff (d.reset)
    d.write_en ##1 (d.read_addr==$past(d.write_addr)));

  // Coverage: reset initializes an addressed location
  cover property (d.reset);
endmodule

// input_signal_detection checks: prev register, exact output condition, coverage
module sva_isd (input_signal_detection i);
  default clocking cb @(posedge i.clk); endclocking
  bit init; always_ff @(posedge i.clk) init <= 1'b1;

  // prev_in captures previous cycle input
  assert property (disable iff (!init) i.prev_in == $past(i.in));

  // Exact output equivalence
  assert property (i.out == ((i.prev_in==4'b0001 && i.in==4'b0000) ? 4'hF : 4'h0));

  // Temporal form: pattern 0001 -> 0000 raises out==F at second cycle
  assert property (disable iff (!init)
                   ($past(i.in)==4'b0001 && i.in==4'b0000) |-> i.out==4'hF);

  // Otherwise out==0
  assert property (!($past(i.in)==4'b0001 && i.in==4'b0000) |-> i.out==4'h0);

  // Coverage: detect event occurs
  cover property (disable iff (!init) ($past(i.in)==4'b0001 && i.in==4'b0000));
endmodule

// functional_module checks: gating logic, coverage
module sva_fm (functional_module f);
  // Pure combinational relation holds at all times
  assert property (f.out == ((f.in_detect != 4'h0) ? f.ram_data : 4'h0));

  // Coverage: both gated and blocked cases
  cover property (f.in_detect==4'h0 && f.out==4'h0);
  cover property (f.in_detect==4'hF && f.out==f.ram_data);
endmodule

// Bind SVA to DUT and submodules
bind top_module         sva_top        sva_top_i      (.*);
bind dual_port_ram      sva_dp_ram     sva_dp_ram_i   (.*);
bind input_signal_detection sva_isd    sva_isd_i      (.*);
bind functional_module  sva_fm         sva_fm_i       (.*);