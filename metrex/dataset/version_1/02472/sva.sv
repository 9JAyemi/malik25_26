// SVA for coordinate_cordic
// Bind into the DUT to access internals without modifying RTL
bind coordinate_cordic cordic_sva();

module cordic_sva;
  // Use DUT clock
  default clocking cb @ (posedge clk); endclocking

  // Shorthand
  localparam int MSB = MIDWIDTH-1;

  // Basic well-formedness: no X on outputs once pipeline is fed with known inputs for 13 cycles
  property stable_inputs_13;
    !$isunknown({realIn,imagIn}) throughout [0:12] and $stable({realIn,imagIn}) [*13];
  endproperty
  assert property (stable_inputs_13 |-> !$isunknown({amplitude,angle}));

  // Combinational pre-rotation mapping assertions
  assert property (!$isunknown({realIn,imagIn}) |-> 
                   reIn == (realIn[INWIDTH-1] ? (imagIn[INWIDTH-1] ? -$signed(imagIn) : $signed(imagIn))
                                              : $signed(realIn)));
  assert property (!$isunknown({realIn,imagIn}) |-> 
                   imIn == (realIn[INWIDTH-1] ? (imagIn[INWIDTH-1] ? $signed(realIn) : -$signed(realIn))
                                              : $signed(imagIn)));
  assert property (!$isunknown({realIn,imagIn}) |-> 
                   ang  == (realIn[INWIDTH-1] ? (imagIn[INWIDTH-1] ? -$signed(HALFPI) : $signed(HALFPI))
                                              : '0));

  // Output mapping assertions
  assert property (amplitude == {xData12[MSB], xData12[MSB-2:0]});
  assert property (angle     == angle12);
  // test bus mapping
  assert property (test2 == test1);

  // Stage 1 (uses current reIn/imIn/ang)
  assert property (!$isunknown({reIn,imIn,ang}) |->
    ( xData1 == (imIn[MSB] ? (reIn - imIn) : (reIn + imIn)) ) &&
    ( yData1 == (imIn[MSB] ? (imIn + reIn) : (imIn - reIn)) ) &&
    ( angle1 == (imIn[MSB] ? (ang - ARCTANG_0) : (ang + ARCTANG_0)) )
  );

  // Macro to reduce repetition for stages 2..12
`define STAGE_CHECK(K, KP, SH, ARC) \
  assert property ( !$isunknown($past({xData``KP, yData``KP, angle``KP})) |->
    ( xData``K == ( $past(yData``KP[MSB]) ? ($past(xData``KP) - {{SH{$past(yData``KP[MSB])}}, $past(yData``KP)[MSB-1:SH]}) \
                                          : ($past(xData``KP) + {{SH{$past(yData``KP[MSB])}}, $past(yData``KP)[MSB-1:SH]}) ) ) && \
    ( yData``K == ( $past(yData``KP[MSB]) ? ($past(yData``KP) + {{SH{$past(xData``KP[MSB])}}, $past(xData``KP)[MSB-1:SH]}) \
                                          : ($past(yData``KP) - {{SH{$past(xData``KP[MSB])}}, $past(xData``KP)[MSB-1:SH]}) ) ) && \
    ( angle``K == ( $past(yData``KP[MSB]) ? ($past(angle``KP) - ARC) : ($past(angle``KP) + ARC) ) ) \
  );

  // Stages 2..12 (shift amounts 1..11 respectively)
  `STAGE_CHECK(2, 1, 1, ARCTANG_1)
  `STAGE_CHECK(3, 2, 2, ARCTANG_2)
  `STAGE_CHECK(4, 3, 3, ARCTANG_3)
  `STAGE_CHECK(5, 4, 4, ARCTANG_4)
  `STAGE_CHECK(6, 5, 5, ARCTANG_5)
  `STAGE_CHECK(7, 6, 6, ARCTANG_6)
  `STAGE_CHECK(8, 7, 7, ARCTANG_7)
  `STAGE_CHECK(9, 8, 8, ARCTANG_8)
  `STAGE_CHECK(10, 9, 9, ARCTANG_9)
  `STAGE_CHECK(11, 10, 10, ARCTANG_10)
  `STAGE_CHECK(12, 11, 11, ARCTANG_11)

  // No-X on key stage registers once pipeline is fed (after 12 cycles of known inputs)
  assert property (stable_inputs_13 |-> !$isunknown({xData12,yData12,angle12}));

  // Functional coverage: exercise both directions at each stage and all input quadrants
  cover property (imIn[MSB] == 1'b0);
  cover property (imIn[MSB] == 1'b1);
  cover property (realIn[INWIDTH-1] == 0 && imagIn[INWIDTH-1] == 0);
  cover property (realIn[INWIDTH-1] == 0 && imagIn[INWIDTH-1] == 1);
  cover property (realIn[INWIDTH-1] == 1 && imagIn[INWIDTH-1] == 0);
  cover property (realIn[INWIDTH-1] == 1 && imagIn[INWIDTH-1] == 1);

`define DIR_COV(KP) \
  cover property (yData``KP[MSB] == 1'b0); \
  cover property (yData``KP[MSB] == 1'b1);

  `DIR_COV(1)  `DIR_COV(2)  `DIR_COV(3)  `DIR_COV(4)  `DIR_COV(5)  `DIR_COV(6)
  `DIR_COV(7)  `DIR_COV(8)  `DIR_COV(9)  `DIR_COV(10) `DIR_COV(11)

  // Simple activity covers
  cover property (amplitude != '0);
  cover property (angle     != '0);
endmodule