// SVA for bmu: concise, full functional checking and coverage
module bmu_sva (
  input        cx0, cx1,
  input [1:0]  bm0, bm1, bm2, bm3, bm4, bm5, bm6, bm7
);
  // Sample on any input edge; use ##0 to see post-NBA values
  localparam int unsigned VECW = 16;
  wire [VECW-1:0] bm_vec = {bm0,bm1,bm2,bm3,bm4,bm5,bm6,bm7};
  `define ANYEDGE  (posedge cx0 or negedge cx0 or posedge cx1 or negedge cx1)

  // No X/Z on outputs when inputs are known
  property p_no_xz;
    @(`ANYEDGE) disable iff ($isunknown({cx0,cx1}))
      1'b1 |-> ##0 !$isunknown(bm_vec);
  endproperty
  assert property (p_no_xz);

  // Outputs never take value 2'd3
  property p_no_3;
    @(`ANYEDGE) disable iff ($isunknown({cx0,cx1}))
      1'b1 |-> ##0 (bm0!=2'd3 && bm1!=2'd3 && bm2!=2'd3 && bm3!=2'd3 &&
                    bm4!=2'd3 && bm5!=2'd3 && bm6!=2'd3 && bm7!=2'd3);
  endproperty
  assert property (p_no_3);

  // Functional mapping checks (and coverage)
  // 00 -> 16'h2855
  property p_map_00;
    @(`ANYEDGE) disable iff ($isunknown({cx0,cx1}))
      ({cx0,cx1}==2'b00) |-> ##0 (bm_vec==16'h2855);
  endproperty
  assert property (p_map_00);
  cover  property (p_map_00);

  // 01 -> 16'h5582
  property p_map_01;
    @(`ANYEDGE) disable iff ($isunknown({cx0,cx1}))
      ({cx0,cx1}==2'b01) |-> ##0 (bm_vec==16'h5582);
  endproperty
  assert property (p_map_01);
  cover  property (p_map_01);

  // 10 -> 16'h5528
  property p_map_10;
    @(`ANYEDGE) disable iff ($isunknown({cx0,cx1}))
      ({cx0,cx1}==2'b10) |-> ##0 (bm_vec==16'h5528);
  endproperty
  assert property (p_map_10);
  cover  property (p_map_10);

  // 11 -> 16'h8255
  property p_map_11;
    @(`ANYEDGE) disable iff ($isunknown({cx0,cx1}))
      ({cx0,cx1}==2'b11) |-> ##0 (bm_vec==16'h8255);
  endproperty
  assert property (p_map_11);
  cover  property (p_map_11);

  // Optional: one consolidated coverage for seeing all four input combos
  cover property (@(`ANYEDGE) ! $isunknown({cx0,cx1}) ##0 1)
    iff (! $isunknown({cx0,cx1}));
endmodule

// Bind into DUT
bind bmu bmu_sva bmu_sva_i (.*);