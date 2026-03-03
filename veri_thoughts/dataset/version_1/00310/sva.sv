// SVA for the given design. Bind into the DUT; no DUT/testbench changes needed.

module sva_v3676a0 (input vcbab45, input v0e28cb);
  // Equivalence and X-prop (NBA-safe with #0)
  always @* assert (#0 (v0e28cb === vcbab45)) else $error("v3676a0: v0e28cb != vcbab45");
  always @* if (!$isunknown(vcbab45)) assert (#0 !$isunknown(v0e28cb)) else $error("v3676a0: X on v0e28cb with known input");
  // Coverage
  cover property (@(posedge v0e28cb) 1);
  cover property (@(negedge v0e28cb) 1);
endmodule

module sva_vba518e (input vcbab45, input v0e28cb, input v3ca442);
  always @* assert (#0 (v0e28cb === (vcbab45 & v3ca442))) else $error("vba518e: v0e28cb != vcbab45 & v3ca442");
  always @* if (!$isunknown({vcbab45,v3ca442})) assert (#0 !$isunknown(v0e28cb)) else $error("vba518e: X on v0e28cb with known inputs");
  cover property (@(posedge v0e28cb) (vcbab45 && v3ca442));
  cover property (@(negedge v0e28cb) (!vcbab45 || !v3ca442));
endmodule

module sva_v053dc2 (input vf54559, input va4102a, input ve8318d);
  always @* assert (#0 (ve8318d === (vf54559 | va4102a))) else $error("v053dc2: ve8318d != vf54559 | va4102a");
  always @* if (!$isunknown({vf54559,va4102a})) assert (#0 !$isunknown(ve8318d)) else $error("v053dc2: X on ve8318d with known inputs");
  cover property (@(posedge ve8318d) (vf54559 || va4102a));
  cover property (@(negedge ve8318d) (!vf54559 && !va4102a));
endmodule

module sva_v2be0f8 (input vd53b77, input v27dec4, input vf354ee, input v4642b6, input w1);
  // OR output correctness and X-prop
  always @* assert (#0 (v4642b6 === (vd53b77 | v27dec4))) else $error("v2be0f8: v4642b6 != vd53b77 | v27dec4");
  always @* if (!$isunknown({vd53b77,v27dec4})) assert (#0 !$isunknown(v4642b6)) else $error("v2be0f8: X on v4642b6 with known inputs");
  // Internal AND path correctness (through vba518e->v3676a0)
  always @* assert (#0 (w1 === (vd53b77 & vf354ee))) else $error("v2be0f8: w1 != vd53b77 & vf354ee");
  // Coverage
  cover property (@(posedge v4642b6) (vd53b77 || v27dec4));
  cover property (@(negedge v4642b6) (!vd53b77 && !v27dec4));
  cover property (@(posedge w1) (vd53b77 && vf354ee));
  cover property (@(negedge w1) (!vd53b77 || !vf354ee));
endmodule

// Binds
bind v3676a0  sva_v3676a0  sva_v3676a0_b (.vcbab45(vcbab45), .v0e28cb(v0e28cb));
bind vba518e  sva_vba518e  sva_vba518e_b (.vcbab45(vcbab45), .v0e28cb(v0e28cb), .v3ca442(v3ca442));
bind v053dc2  sva_v053dc2  sva_v053dc2_b (.vf54559(vf54559), .va4102a(va4102a), .ve8318d(ve8318d));
bind v2be0f8  sva_v2be0f8  sva_v2be0f8_b (.vd53b77(vd53b77), .v27dec4(v27dec4), .vf354ee(vf354ee), .v4642b6(v4642b6), .w1(w1));