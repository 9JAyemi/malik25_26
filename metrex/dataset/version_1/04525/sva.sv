// Bind this SVA module to the DUT:
// bind butterfly_32 butterfly_32_sva u_butterfly_32_sva();

module butterfly_32_sva;

  // Basic sanity on enable activity
  cover property (@(posedge enable) 1);
  cover property (@(negedge enable) 1);

  // Macro to assert sum/diff correctness, muxing by enable, pass-through sign-extension, and basic X-prop
  `define BF_PAIR(IA, IB, BS, BD, OS, OD) \
    assert property (@(*) (!$isunknown({IA,IB})) |-> \
                      ($signed(BS) == $signed(IA) + $signed(IB)) && \
                      ($signed(BD) == $signed(IA) - $signed(IB))); \
    assert property (@(*) (enable)  |-> (OS == BS && OD == BD)); \
    assert property (@(*) (!enable) |-> (OS[26:0] == IA && OS[27] == IA[26] && \
                                         OD[26:0] == IB && OD[27] == IB[26])); \
    assert property (@(*) (!$isunknown(enable) && !$isunknown({IA,IB})) |-> \
                          !$isunknown({OS,OD})); \
    cover  property (@(*) enable && (BS == '0)); \
    cover  property (@(*) enable && (BD == '0))

  // 16 symmetric butterfly pairs
  `BF_PAIR(i_0 , i_31, b_0 , b_31, o_0 , o_31);
  `BF_PAIR(i_1 , i_30, b_1 , b_30, o_1 , o_30);
  `BF_PAIR(i_2 , i_29, b_2 , b_29, o_2 , o_29);
  `BF_PAIR(i_3 , i_28, b_3 , b_28, o_3 , o_28);
  `BF_PAIR(i_4 , i_27, b_4 , b_27, o_4 , o_27);
  `BF_PAIR(i_5 , i_26, b_5 , b_26, o_5 , o_26);
  `BF_PAIR(i_6 , i_25, b_6 , b_25, o_6 , o_25);
  `BF_PAIR(i_7 , i_24, b_7 , b_24, o_7 , o_24);
  `BF_PAIR(i_8 , i_23, b_8 , b_23, o_8 , o_23);
  `BF_PAIR(i_9 , i_22, b_9 , b_22, o_9 , o_22);
  `BF_PAIR(i_10, i_21, b_10, b_21, o_10, o_21);
  `BF_PAIR(i_11, i_20, b_11, b_20, o_11, o_20);
  `BF_PAIR(i_12, i_19, b_12, b_19, o_12, o_19);
  `BF_PAIR(i_13, i_18, b_13, b_18, o_13, o_18);
  `BF_PAIR(i_14, i_17, b_14, b_17, o_14, o_17);
  `BF_PAIR(i_15, i_16, b_15, b_16, o_15, o_16);

endmodule