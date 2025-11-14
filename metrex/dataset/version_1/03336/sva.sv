// SVA for arithmetic_operations
// Quality-focused, concise checks and coverage
// Bind into DUT to access internals by name

module arithmetic_operations_sva;

  // Drive from DUT clock domain
  default clocking cb @(posedge CLK); endclocking

  // Guard $past at time 0
  bit init;
  always_ff @(posedge CLK) init <= 1'b1;

  // Local widths
  localparam int DRW  = $bits(DR);
  localparam int DIW  = $bits(DI);
  localparam int DX5W = $bits(dx5);
  localparam int DX7W = $bits(dx7);
  localparam int DTW  = $bits(dt);
  localparam int DOOW = $bits(doo);
  localparam int DOTW = $bits(dot);

  // Helper lets (sized-extensions where needed)
  let zext_dr_to_dx5 = {{(DX5W-DRW){1'b0}}, (DR + (DR << 2))};
  let dii_sum5       = (dii + (dii <<< 2));
  let sext_dii_to_dx5= {{(DX5W-DIW){dii_sum5[DIW-1]}}, dii_sum5};
  let sext_dii_to_dt = {{(DTW -DIW){dii[DIW-1]}}, dii};
  let zext_dr_to_dt  = {{(DTW -DRW){1'b0}}, DR};
  let doo_neg        = $unsigned(-$signed(doo));
  let dot_shr3_low   = ($signed(dot) >>> 3)[DOOW-1:0];

  // Structural: hold state when ED==0
  assert property (disable iff (!init) !ED |=> $stable({edd,edd2,edd3, mpyjd,mpyjd2,mpyjd3,
                                                       dx5,dx7,dt,dii, doo,droo, DOR,DOI}));

  // Shift-register pipelines (valid only when ED)
  assert property (disable iff (!init) ED |-> edd   == $past(DS));
  assert property (disable iff (!init) ED |-> edd2  == $past(edd));
  assert property (disable iff (!init) ED |-> edd3  == $past(edd2));
  assert property (disable iff (!init) ED |-> mpyjd  == $past(MPYJ));
  assert property (disable iff (!init) ED |-> mpyjd2 == $past(mpyjd));
  assert property (disable iff (!init) ED |-> mpyjd3 == $past(mpyjd2));

  // Data-path state updates (use same-cycle inputs/regs as in DUT nonblocking semantics)
  assert property (disable iff (!init) ED &&  DS |-> dx5 == $past(zext_dr_to_dx5));
  assert property (disable iff (!init) ED && !DS |-> dx5 == $past(sext_dii_to_dx5));
  assert property (disable iff (!init) ED &&  DS |-> dx7 == $past( DR - (DR >>> 3)));
  assert property (disable iff (!init) ED && !DS |-> dx7 == $past( dii - (dii >>> 3)));
  assert property (disable iff (!init) ED &&  DS |-> dt  == $past(zext_dr_to_dt));
  assert property (disable iff (!init) ED && !DS |-> dt  == $past(sext_dii_to_dt));
  assert property (disable iff (!init) ED &&  DS |-> dii == $past(DI));
  assert property (disable iff (!init) ED && !DS |-> $stable(dii));

  // Combinational wires sanity (signed math as intended)
  assert property ($signed(dx5p) == ($signed(dx5) <<< 1) + ($signed(dx7) >>> 1));
  assert property ($signed(dot)  == $signed(dx5p) + ($signed(dt) >>> 6) - ($signed(dx5) >>> 13));

  // doo/droo pipeline
  assert property (disable iff (!init) ED |-> doo  == $past(dot_shr3_low));
  assert property (disable iff (!init) ED |-> droo == $past(doo));

  // Output update protocol and mapping
  assert property (disable iff (!init) ED && !edd3 |-> $stable({DOR,DOI}));
  assert property (disable iff (!init) ED && edd3  |-> DOR == $past(mpyjd3 ? doo : droo));
  assert property (disable iff (!init) ED && edd3  |-> DOI == $past(mpyjd3 ? doo_neg : doo));

  // X-prop checks on active cycles
  assert property (ED |-> !$isunknown({DS,MPYJ}));                       // control known when enabled
  assert property (ED && DS |-> !$isunknown({DR,DI}));                    // inputs known when sampled
  assert property (ED |-> !$isunknown({dot,doo,droo}));                   // internal datapath known on enable
  assert property (ED && edd3 |-> !$isunknown({DOR,DOI}));                // outputs known when driven

  // Minimal but meaningful coverage
  cover property (ED && DS);                 // DR/DI sample path exercised
  cover property (ED && !DS);                // dii reuse path exercised
  cover property (ED ##1 ED ##1 ED && edd3); // output gating active after pipeline fill
  cover property (ED && edd3 && mpyjd3);     // MPYJ branch: conjugate path
  cover property (ED && edd3 && !mpyjd3);    // MPYJ branch: direct path

endmodule

bind arithmetic_operations arithmetic_operations_sva;