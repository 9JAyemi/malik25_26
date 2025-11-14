module barrel_shifter_sva;

  // Bound into barrel_shifter; can see internal signals
  function automatic [7:0] exp (input [7:0] d, input [2:0] a, input dir);
    exp = dir ? (d >> a) : (d << a);
  endfunction

  // Functional equivalence after delta when inputs are known and change
  property p_func;
    (!$isunknown({DATA,SHIFT_AMOUNT,SHIFT_DIRECTION}) &&
     $changed({DATA,SHIFT_AMOUNT,SHIFT_DIRECTION})) |-> ##0
       (SHIFTED_DATA == exp(DATA,SHIFT_AMOUNT,SHIFT_DIRECTION));
  endproperty
  assert property (p_func);

  // Stage 0 computes the same function as the DUT spec
  property p_stage0;
    (!$isunknown({DATA,SHIFT_AMOUNT,SHIFT_DIRECTION}) &&
     $changed({DATA,SHIFT_AMOUNT,SHIFT_DIRECTION})) |-> ##0
       (pipeline_reg[0] == exp(DATA,SHIFT_AMOUNT,SHIFT_DIRECTION));
  endproperty
  assert property (p_stage0);

  // Pure pass-through between pipeline stages (combinational)
  property p_stage1_passthru;
    (!$isunknown(pipeline_reg[0]) && $changed(pipeline_reg[0])) |-> ##0
      (pipeline_reg[1] == pipeline_reg[0]);
  endproperty
  assert property (p_stage1_passthru);

  property p_stage2_passthru;
    (!$isunknown(pipeline_reg[1]) && $changed(pipeline_reg[1])) |-> ##0
      (pipeline_reg[2] == pipeline_reg[1]);
  endproperty
  assert property (p_stage2_passthru);

  // If inputs are known, output must be known after settle
  property p_no_x_on_output;
    (!$isunknown({DATA,SHIFT_AMOUNT,SHIFT_DIRECTION})) |-> ##0
      (!$isunknown(SHIFTED_DATA));
  endproperty
  assert property (p_no_x_on_output);

  // Coverage: directions and key shift amounts
  cover property (!$isunknown({DATA,SHIFT_AMOUNT,SHIFT_DIRECTION}) && (SHIFT_DIRECTION == 1'b0));
  cover property (!$isunknown({DATA,SHIFT_AMOUNT,SHIFT_DIRECTION}) && (SHIFT_DIRECTION == 1'b1));
  cover property (!$isunknown({DATA,SHIFT_AMOUNT,SHIFT_DIRECTION}) && (SHIFT_AMOUNT == 3'd0) &&
                  (SHIFTED_DATA == DATA));
  cover property (!$isunknown({DATA,SHIFT_AMOUNT,SHIFT_DIRECTION}) && (SHIFT_DIRECTION==1'b0) &&
                  (SHIFT_AMOUNT == 3'd7) && (SHIFTED_DATA == (DATA << 3'd7)));
  cover property (!$isunknown({DATA,SHIFT_AMOUNT,SHIFT_DIRECTION}) && (SHIFT_DIRECTION==1'b1) &&
                  (SHIFT_AMOUNT == 3'd7) && (SHIFTED_DATA == (DATA >> 3'd7)));
  cover property (!$isunknown({DATA,SHIFT_AMOUNT,SHIFT_DIRECTION}) && (SHIFT_DIRECTION==1'b0) &&
                  (SHIFT_AMOUNT inside {[3'd1:3'd7]}) &&
                  ((SHIFTED_DATA & ((8'h01 << SHIFT_AMOUNT) - 8'h01)) == 8'h00)); // zero-fill LSBs
  cover property (!$isunknown({DATA,SHIFT_AMOUNT,SHIFT_DIRECTION}) && (SHIFT_DIRECTION==1'b1) &&
                  (SHIFT_AMOUNT inside {[3'd1:3'd7]}) &&
                  ((SHIFTED_DATA & ~(8'hFF >> SHIFT_AMOUNT)) == 8'h00)); // zero-fill MSBs

endmodule

bind barrel_shifter barrel_shifter_sva barrel_shifter_sva_i();