// SVA checker for select_logic
module select_logic_sva(
  input i1, i2, i3, i4, i5, i6, i7, i8,
  input s1, s2, s3,
  input a1
);
  // Helper minterms and select
  wire m1 = ~s1 & ~s2 & ~s3;
  wire m2 = ~s1 & ~s2 &  s3;
  wire m3 = ~s1 &  s2 & ~s3;
  wire m4 = ~s1 &  s2 &  s3;
  wire m5 =  s1 & ~s2 & ~s3;
  wire m6 =  s1 & ~s2 &  s3;
  wire m7 =  s1 &  s2 & ~s3;
  wire m8 =  s1 &  s2 &  s3;
  wire [2:0] sel = {s1,s2,s3};

  // Select decoding is mutually exclusive and complete
  assert property ( $onehot({m1,m2,m3,m4,m5,m6,m7,m8}) );

  // No X on selects or output
  assert property ( !$isunknown({s1,s2,s3}) );
  assert property ( !$isunknown(a1) );

  // Functional correctness (concise mux form)
  assert property ( a1 == (sel==3'b000 ? i1 :
                           sel==3'b001 ? i2 :
                           sel==3'b010 ? i3 :
                           sel==3'b011 ? i4 :
                           sel==3'b100 ? i5 :
                           sel==3'b101 ? i6 :
                           sel==3'b110 ? i7 : i8) );

  // Functional correctness (SOP equivalence)
  assert property ( a1 == ((i1 & m1) | (i2 & m2) | (i3 & m3) | (i4 & m4) |
                           (i5 & m5) | (i6 & m6) | (i7 & m7) | (i8 & m8)) );

  // Localized checks per select code
  assert property ( (sel==3'b000) |-> (a1==i1) );
  assert property ( (sel==3'b001) |-> (a1==i2) );
  assert property ( (sel==3'b010) |-> (a1==i3) );
  assert property ( (sel==3'b011) |-> (a1==i4) );
  assert property ( (sel==3'b100) |-> (a1==i5) );
  assert property ( (sel==3'b101) |-> (a1==i6) );
  assert property ( (sel==3'b110) |-> (a1==i7) );
  assert property ( (sel==3'b111) |-> (a1==i8) );

  // Coverage: each select combination observed with correct mapping
  cover property ( (sel==3'b000) && (a1==i1) );
  cover property ( (sel==3'b001) && (a1==i2) );
  cover property ( (sel==3'b010) && (a1==i3) );
  cover property ( (sel==3'b011) && (a1==i4) );
  cover property ( (sel==3'b100) && (a1==i5) );
  cover property ( (sel==3'b101) && (a1==i6) );
  cover property ( (sel==3'b110) && (a1==i7) );
  cover property ( (sel==3'b111) && (a1==i8) );
endmodule

// Bind into DUT
bind select_logic select_logic_sva sva_select_logic (.*);