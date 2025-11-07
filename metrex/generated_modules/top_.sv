// SVA for this design. Bind these to the DUT files.

// Top-level checks
module top_module_sva;
  default clocking cb @(posedge clk); endclocking

  // Sign-magnitude conversion checks
  a_mag_pos: assert property (a[7]==0 |-> a_mag == a);
  a_mag_neg: assert property (a[7]==1 |-> (a_mag[7]==0 && a_mag[6:0] == (~a[6:0] + 1)));

  b_mag_pos: assert property (b[7]==0 |-> b_mag == b);
  b_mag_neg: assert property (b[7]==1 |-> (b_mag[7]==0 && b_mag[6:0] == (~b[6:0] + 1)));

  // Output selection and tie-offs
  cin_tied_low: assert property (adder_inst.cin == 1'b0);
  ovf_wire:     assert property (overflow == adder_overflow);
  sel_add:      assert property (select==0 |-> s == adder_out[7:0]);
  sel_shift:    assert property (select==1 |-> (s == {4'b0, shift_out} && s[7:4]==4'b0));

  // Shift register interface constants from top
  en_const:   assert property (shift_inst.enable == 1'b1);
  load_const: assert property (shift_inst.load   == 1'b0);

  // Shift behavior (active-low reset from shift_register)
  left_shift:  assert property (disable iff (!reset)  select && shift_inst.enable && !shift_inst.load |=> shift_out == {$past(shift_out)[2:0],1'b0});
  right_shift: assert property (disable iff (!reset) !select && shift_inst.enable && !shift_inst.load |=> shift_out == {1'b0,$past(shift_out)[3:1]});
  hold_in_reset: assert property (@(posedge clk) !reset |-> shift_out == 4'b0);

  // Basic functional coverage
  cover_sel_01: cover property (select==0 ##1 select==1);
  cover_sel_10: cover property (select==1 ##1 select==0);
  cover_ovf:    cover property (overflow);
  cover_a_neg:  cover property (a[7]);
  cover_b_neg:  cover property (b[7]);
endmodule

// Adder-local checks (combinational)
module carry_select_adder_sva;
  // Core relation (using recomputed p/g to avoid hierarchy to internal wires)
  always @* begin
    assert ((cin==1'b0 && s == ((a+b) + ((a&b)<<1))) ||
            (cin==1'b1 && s == ((a+b) - ((a&b)<<1))))
      else $error("carry_select_adder: s mismatch");
    assert (cout == (((a&b)[6]) | ((a&b)[5] & cin)))
      else $error("carry_select_adder: cout mismatch");
    assert (overflow == ((a[7]==b[7]) && (s[7] != a[7])))
      else $error("carry_select_adder: overflow mismatch");
    assert (s[8] == 1'b0) // zero-extended assignment to 9-bit s
      else $error("carry_select_adder: s[8] not zero");
  end

  // Minimal coverage
  cover_cin0: cover property (@(posedge $root.top_module.clk) cin==0);
  cover_cin1: cover property (@(posedge $root.top_module.clk) cin==1);
  cover_ovf:  cover property (@(posedge $root.top_module.clk) overflow);
endmodule

// Shift-register-local checks
module shift_register_sva;
  default clocking cb @(posedge clk); endclocking

  // Asynchronous active-low reset behavior
  async_reset_clears: assert property (@(negedge reset) ##[0:1] q == 4'b0);
  while_in_reset:     assert property (!reset |-> q == 4'b0);

  // One-cycle next-state behavior
  hold_when_disabled:       assert property (disable iff (!reset) !enable |=> q == $past(q));
  load_when_enabled:        assert property (disable iff (!reset)  enable && load |=> q == $past(data));
  shift_left_when_enabled:  assert property (disable iff (!reset)  enable && !load && shift_left |=> q == {$past(q)[2:0],1'b0});
  shift_right_when_enabled: assert property (disable iff (!reset)  enable && !load && !shift_left |=> q == {1'b0,$past(q)[3:1]});

  // Coverage of key modes
  cover_load:  cover property (disable iff (!reset) enable && load);
  cover_lsh:   cover property (disable iff (!reset) enable && !load && shift_left);
  cover_rsh:   cover property (disable iff (!reset) enable && !load && !shift_left);
  cover_arst:  cover property (@(negedge reset) 1);
endmodule

// Binds
bind top_module         top_module_sva        top_module_sva_i();
bind carry_select_adder carry_select_adder_sva csa_sva_i();
bind shift_register     shift_register_sva     sh_sva_i();