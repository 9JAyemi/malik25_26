// synthesis translate_off
// SVA for my_module: functional correctness, power sanity, and concise coverage
module my_module_assertions (my_module dut);

  // Sample whenever any relevant signal changes
  default clocking cb @(
    dut.in_wire1 or dut.in_wire2 or dut.in_wire3 or
    dut.out_wire or dut.Y or
    dut.power or dut.ground or dut.power_bond or dut.ground_bond
  ); endclocking

  // Helpers
  let PG      = (dut.power===1'b1) && (dut.ground===1'b0) &&
                (dut.power_bond===dut.power) && (dut.ground_bond===dut.ground);
  let IN_KN   = !$isunknown({dut.in_wire1,dut.in_wire2,dut.in_wire3});
  let OUT_EXP = (dut.in_wire1 ^ (dut.in_wire2 | dut.in_wire3));
  let Y_EXP   = ~(((dut.in_wire1 | dut.in_wire2)) & dut.in_wire3);

  // Power/bias sanity
  ap_power_known: assert property ( !$isunknown({dut.power,dut.ground,dut.power_bond,dut.ground_bond}) );
  ap_body_tied:   assert property ( (dut.power===1'b1 && dut.ground===1'b0) |-> (dut.power_bond==dut.power && dut.ground_bond==dut.ground) );

  // Functional correctness (under power-good and known inputs)
  ap_out_func: assert property ( PG && IN_KN |-> (dut.out_wire == OUT_EXP) );
  ap_y_func:   assert property ( PG && IN_KN |-> (dut.Y == Y_EXP) );

  // No spurious changes when inputs are stable (under PG)
  ap_stable_out: assert property ( PG && $stable({dut.in_wire1,dut.in_wire2,dut.in_wire3}) |=> $stable(dut.out_wire) );
  ap_stable_y:   assert property ( PG && $stable({dut.in_wire1,dut.in_wire2,dut.in_wire3}) |=> $stable(dut.Y) );

  // Output changes must be driven by input changes (under PG)
  ap_out_cause: assert property ( PG && $changed(dut.out_wire) |-> $changed({dut.in_wire1,dut.in_wire2,dut.in_wire3}) );
  ap_y_cause:   assert property ( PG && $changed(dut.Y)       |-> $changed({dut.in_wire1,dut.in_wire2,dut.in_wire3}) );

  // Full input-space coverage (under PG)
  cover_000: cover property ( PG && {dut.in_wire1,dut.in_wire2,dut.in_wire3}==3'b000 && dut.out_wire==OUT_EXP && dut.Y==Y_EXP );
  cover_001: cover property ( PG && {dut.in_wire1,dut.in_wire2,dut.in_wire3}==3'b001 && dut.out_wire==OUT_EXP && dut.Y==Y_EXP );
  cover_010: cover property ( PG && {dut.in_wire1,dut.in_wire2,dut.in_wire3}==3'b010 && dut.out_wire==OUT_EXP && dut.Y==Y_EXP );
  cover_011: cover property ( PG && {dut.in_wire1,dut.in_wire2,dut.in_wire3}==3'b011 && dut.out_wire==OUT_EXP && dut.Y==Y_EXP );
  cover_100: cover property ( PG && {dut.in_wire1,dut.in_wire2,dut.in_wire3}==3'b100 && dut.out_wire==OUT_EXP && dut.Y==Y_EXP );
  cover_101: cover property ( PG && {dut.in_wire1,dut.in_wire2,dut.in_wire3}==3'b101 && dut.out_wire==OUT_EXP && dut.Y==Y_EXP );
  cover_110: cover property ( PG && {dut.in_wire1,dut.in_wire2,dut.in_wire3}==3'b110 && dut.out_wire==OUT_EXP && dut.Y==Y_EXP );
  cover_111: cover property ( PG && {dut.in_wire1,dut.in_wire2,dut.in_wire3}==3'b111 && dut.out_wire==OUT_EXP && dut.Y==Y_EXP );

  // Toggle coverage
  cover_out_rise: cover property ( PG && $rose(dut.out_wire) );
  cover_out_fall: cover property ( PG && $fell(dut.out_wire) );
  cover_y_rise:   cover property ( PG && $rose(dut.Y) );
  cover_y_fall:   cover property ( PG && $fell(dut.Y) );

endmodule

bind my_module my_module_assertions sva_my_module();
// synthesis translate_on