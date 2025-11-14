// SVA for spiral_16: concise, combinational reference checks + key coverage.
// Bind this to the DUT.
bind spiral_16 spiral_16_sva sva();

module spiral_16_sva (spiral_16 dut);

  typedef logic signed [16:0] s17;
  typedef logic signed [23:0] s24;
  typedef logic signed [22:0] s23;

  function automatic s24 sext17_to24 (s17 a);
    return {{7{a[16]}},a};
  endfunction

  function automatic s23 trunc23 (s24 a);
    return a[22:0];
  endfunction

  // Reference model (24-bit signed math, then truncate to 23b like DUT does)
  s24 i24;
  s24 w1,w32,w31,w8,w23x,w4,w27,w39,w62,w61x,w9,w2x,w11,w13x,w18,w19,w41,w36,w45,w67x,w64,w73x,w16,w17,w68,w85x,w22x,w38x,w46x,w54x,w78x,w82x,w88x,w90x;
  s23 e4,e13,e22,e31,e38,e46,e54,e61,e67,e73,e78,e82,e85,e88,e90;

  always_comb begin
    i24  = sext17_to24(dut.i_data);
    w1   = i24;
    w32  = w1 <<< 5;
    w31  = w32 - w1;
    w8   = w1 <<< 3;
    w23x = w31 - w8;
    w4   = w1 <<< 2;
    w27  = w31 - w4;
    w39  = w31 + w8;
    w62  = w31 <<< 1;
    w61x = w62 - w1;
    w9   = w1 + w8;
    w2x  = w1 <<< 1;
    w11  = w9 + w2x;
    w13x = w9 + w4;
    w18  = w9 <<< 1;
    w19  = w1 + w18;
    w41  = w9 + w32;
    w36  = w9 <<< 2;
    w45  = w9 + w36;
    w67x = w31 + w36;
    w64  = w1 <<< 6;
    w73x = w9 + w64;
    w16  = w1 <<< 4;
    w17  = w1 + w16;
    w68  = w17 <<< 2;
    w85x = w17 + w68;
    w22x = w11 <<< 1;
    w38x = w19 <<< 1;
    w46x = w23x <<< 1;
    w54x = w27 <<< 1;
    w78x = w39 <<< 1;
    w82x = w41 <<< 1;
    w88x = w11 <<< 3;
    w90x = w45 <<< 1;

    e4   = trunc23(w4);
    e13  = trunc23(w13x);
    e22  = trunc23(w22x);
    e31  = trunc23(w31);
    e38  = trunc23(w38x);
    e46  = trunc23(w46x);
    e54  = trunc23(w54x);
    e61  = trunc23(w61x);
    e67  = trunc23(w67x);
    e73  = trunc23(w73x);
    e78  = trunc23(w78x);
    e82  = trunc23(w82x);
    e85  = trunc23(w85x);
    e88  = trunc23(w88x);
    e90  = trunc23(w90x);

    // X/Z checks
    assert (!$isunknown(dut.i_data)) else $error("spiral_16: i_data has X/Z");
    assert (!$isunknown(dut.o_data_4 )) else $error("spiral_16: o_data_4 has X/Z");
    assert (!$isunknown(dut.o_data_13)) else $error("spiral_16: o_data_13 has X/Z");
    assert (!$isunknown(dut.o_data_22)) else $error("spiral_16: o_data_22 has X/Z");
    assert (!$isunknown(dut.o_data_31)) else $error("spiral_16: o_data_31 has X/Z");
    assert (!$isunknown(dut.o_data_38)) else $error("spiral_16: o_data_38 has X/Z");
    assert (!$isunknown(dut.o_data_46)) else $error("spiral_16: o_data_46 has X/Z");
    assert (!$isunknown(dut.o_data_54)) else $error("spiral_16: o_data_54 has X/Z");
    assert (!$isunknown(dut.o_data_61)) else $error("spiral_16: o_data_61 has X/Z");
    assert (!$isunknown(dut.o_data_67)) else $error("spiral_16: o_data_67 has X/Z");
    assert (!$isunknown(dut.o_data_73)) else $error("spiral_16: o_data_73 has X/Z");
    assert (!$isunknown(dut.o_data_78)) else $error("spiral_16: o_data_78 has X/Z");
    assert (!$isunknown(dut.o_data_82)) else $error("spiral_16: o_data_82 has X/Z");
    assert (!$isunknown(dut.o_data_85)) else $error("spiral_16: o_data_85 has X/Z");
    assert (!$isunknown(dut.o_data_88)) else $error("spiral_16: o_data_88 has X/Z");
    assert (!$isunknown(dut.o_data_90)) else $error("spiral_16: o_data_90 has X/Z");

    // Functional equivalence checks (combinational, 24b ref -> 23b trunc)
    assert (dut.o_data_4  == e4 ) else $error("o_data_4  mismatch exp=%0d got=%0d",  e4,  dut.o_data_4 );
    assert (dut.o_data_13 == e13) else $error("o_data_13 mismatch exp=%0d got=%0d", e13, dut.o_data_13);
    assert (dut.o_data_22 == e22) else $error("o_data_22 mismatch exp=%0d got=%0d", e22, dut.o_data_22);
    assert (dut.o_data_31 == e31) else $error("o_data_31 mismatch exp=%0d got=%0d", e31, dut.o_data_31);
    assert (dut.o_data_38 == e38) else $error("o_data_38 mismatch exp=%0d got=%0d", e38, dut.o_data_38);
    assert (dut.o_data_46 == e46) else $error("o_data_46 mismatch exp=%0d got=%0d", e46, dut.o_data_46);
    assert (dut.o_data_54 == e54) else $error("o_data_54 mismatch exp=%0d got=%0d", e54, dut.o_data_54);
    assert (dut.o_data_61 == e61) else $error("o_data_61 mismatch exp=%0d got=%0d", e61, dut.o_data_61);
    assert (dut.o_data_67 == e67) else $error("o_data_67 mismatch exp=%0d got=%0d", e67, dut.o_data_67);
    assert (dut.o_data_73 == e73) else $error("o_data_73 mismatch exp=%0d got=%0d", e73, dut.o_data_73);
    assert (dut.o_data_78 == e78) else $error("o_data_78 mismatch exp=%0d got=%0d", e78, dut.o_data_78);
    assert (dut.o_data_82 == e82) else $error("o_data_82 mismatch exp=%0d got=%0d", e82, dut.o_data_82);
    assert (dut.o_data_85 == e85) else $error("o_data_85 mismatch exp=%0d got=%0d", e85, dut.o_data_85);
    assert (dut.o_data_88 == e88) else $error("o_data_88 mismatch exp=%0d got=%0d", e88, dut.o_data_88);
    assert (dut.o_data_90 == e90) else $error("o_data_90 mismatch exp=%0d got=%0d", e90, dut.o_data_90);
  end

  // Key concurrent properties and coverage (trigger on any i_data change)
  // Zero-input implies zero-outputs
  property p_zero_maps_to_zero;
    @(dut.i_data)
      (dut.i_data == 17'sd0) |->
      (dut.o_data_4 == 0 && dut.o_data_13 == 0 && dut.o_data_22 == 0 &&
       dut.o_data_31 == 0 && dut.o_data_38 == 0 && dut.o_data_46 == 0 &&
       dut.o_data_54 == 0 && dut.o_data_61 == 0 && dut.o_data_67 == 0 &&
       dut.o_data_73 == 0 && dut.o_data_78 == 0 && dut.o_data_82 == 0 &&
       dut.o_data_85 == 0 && dut.o_data_88 == 0 && dut.o_data_90 == 0);
  endproperty
  assert property (p_zero_maps_to_zero);
  cover  property (p_zero_maps_to_zero);

  // Sign coverage and extremes
  cover property (@(dut.i_data) dut.i_data >  0);
  cover property (@(dut.i_data) dut.i_data <  0);
  cover property (@(dut.i_data) dut.i_data == 17'sd65535);   // max +
  cover property (@(dut.i_data) dut.i_data == -17'sd65536);  // max -

  // Overflow/truncation coverage for high-growth paths
  cover property (@(dut.i_data)
    (w88x[23] != w88x[22]) || (w90x[23] != w90x[22]) ||
    (w85x[23] != w85x[22]) || (w82x[23] != w82x[22]) ||
    (w78x[23] != w78x[22]) || (w73x[23] != w73x[22]) ||
    (w67x[23] != w67x[22]) || (w61x[23] != w61x[22])
  );

endmodule