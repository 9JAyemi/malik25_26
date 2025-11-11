// SVA bind file for functionGen
// Focused, concise checks and coverage

module functionGen_sva #(
  parameter string ARCH               = "GENERIC",
  parameter int    BIT_COMPRESS_PHASE = 1,
  parameter int    BIT_COMPRESS_OUTPUT= 1,
  parameter int    OUT_WIDTH          = 16,
  parameter int    FREQ_WIDTH         = 16,
  parameter int    INCLUDE_CLAMP      = 1
)();

  // Local constants (must match DUT)
  localparam int LOCAL_WIDTH = 18;
  localparam int ANGLE_WIDTH = 10;
  localparam int SINE_WIDTH  = 18;
  localparam int WIDE_WIDTH  = OUT_WIDTH + LOCAL_WIDTH;

  // Access DUT scope signals directly (via bind)
  // clk, rst, en, waveType, freq, phaseOffset, offset, amplitude, outSignal
  // Internal: phaseAcc, phase, unscaledSignal, wideSignalWord, clampedSignal
  //           sdPhase, xorPhase, xorSdPhase, signBit, signBitD1
  //           halfSine, halfSineOrTriangle, sineOrTriangle, sineTable

  bit past_valid;
  initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;

  // Default clock/disable
  `define DIS dis
  property dis; disable iff (rst || !past_valid); 1; endproperty

  // Hold when en==0
  assert property (@(posedge clk) `DIS !en |-> $stable(phaseAcc));
  assert property (@(posedge clk) `DIS !en |-> $stable(phase));
  assert property (@(posedge clk) `DIS !en |-> $stable(unscaledSignal));
  assert property (@(posedge clk) `DIS !en |-> $stable(wideSignalWord));
  assert property (@(posedge clk) `DIS !en |-> $stable(clampedSignal));
  assert property (@(posedge clk) `DIS !en |-> $stable(signBit));
  assert property (@(posedge clk) `DIS !en |-> $stable(signBitD1));
  assert property (@(posedge clk) `DIS !en |-> $stable(halfSine));
  assert property (@(posedge clk) `DIS !en |-> $stable(halfSineOrTriangle));
  assert property (@(posedge clk) `DIS !en |-> $stable(sineOrTriangle));

  // Reset behavior
  assert property (@(posedge clk) rst |-> (phaseAcc=='0 && phase=='0 && unscaledSignal=='0 && wideSignalWord=='0));

  // Phase accumulator and phase update
  assert property (@(posedge clk) `DIS en |-> $past(phaseAcc) + freq == $past(phaseAcc,0) ? $past(phaseAcc) + freq : 1'b0); // keep tool-friendly
  assert property (@(posedge clk) `DIS en |-> (phaseAcc == $past(phaseAcc) + freq));
  assert property (@(posedge clk) `DIS en |-> (phase    == $past(phaseAcc) + phaseOffset));

  // xorPhase mapping (combinational)
  assert property (@(posedge clk) (xorPhase == (phase[FREQ_WIDTH-2] ? ~phase[FREQ_WIDTH-3:0] : phase[FREQ_WIDTH-3:0])));

  // xorSdPhase mapping (combinational with params)
  generate
    if (BIT_COMPRESS_PHASE) begin
      assert property (@(posedge clk) (xorSdPhase == (sdPhase[ANGLE_WIDTH] ? ~sdPhase[ANGLE_WIDTH-1:0] : sdPhase[ANGLE_WIDTH-1:0])));
    end else begin
      if (ANGLE_WIDTH+2 >= FREQ_WIDTH) begin
        assert property (@(posedge clk) (xorSdPhase == (xorPhase << (ANGLE_WIDTH+2-FREQ_WIDTH))));
      end else begin
        assert property (@(posedge clk) (xorSdPhase == (xorPhase >> (FREQ_WIDTH-ANGLE_WIDTH-2))));
      end
    end
  endgenerate

  // signBit pipeline
  assert property (@(posedge clk) `DIS en |-> (signBit   == $past(sdPhase[ANGLE_WIDTH+1])));
  assert property (@(posedge clk) `DIS en |-> (signBitD1 == $past(signBit)));

  // halfSine lookup
  assert property (@(posedge clk) `DIS en |-> (halfSine == $past(sineTable[$past(xorSdPhase)])));

  // halfSineOrTriangle selection/scaling
  generate
    if ((SINE_WIDTH > LOCAL_WIDTH-1) && (FREQ_WIDTH > LOCAL_WIDTH)) begin
      assert property (@(posedge clk) `DIS en |-> (halfSineOrTriangle ==
        ($past(waveType[0]) ? ({$past(xorPhase),1'b1} >> (FREQ_WIDTH-LOCAL_WIDTH))
                            : ($past(halfSine) >> (SINE_WIDTH-LOCAL_WIDTH+1)))));
    end else if ((SINE_WIDTH > LOCAL_WIDTH-1) && (FREQ_WIDTH <= LOCAL_WIDTH)) begin
      assert property (@(posedge clk) `DIS en |-> (halfSineOrTriangle ==
        ($past(waveType[0]) ? ({$past(xorPhase),1'b1} << (LOCAL_WIDTH-FREQ_WIDTH))
                            : ($past(halfSine) >> (SINE_WIDTH-LOCAL_WIDTH+1)))));
    end else if ((SINE_WIDTH <= LOCAL_WIDTH-1) && (FREQ_WIDTH > LOCAL_WIDTH)) begin
      assert property (@(posedge clk) `DIS en |-> (halfSineOrTriangle ==
        ($past(waveType[0]) ? ({$past(xorPhase),1'b1} >> (FREQ_WIDTH-LOCAL_WIDTH))
                            : ($past(halfSine) << (LOCAL_WIDTH-1-SINE_WIDTH)))));
    end else begin
      assert property (@(posedge clk) `DIS en |-> (halfSineOrTriangle ==
        ($past(waveType[0]) ? ({$past(xorPhase),1'b1} << (LOCAL_WIDTH-FREQ_WIDTH))
                            : ($past(halfSine) << (LOCAL_WIDTH-1-SINE_WIDTH)))));
    end
  endgenerate

  // sineOrTriangle reconstruction
  assert property (@(posedge clk) `DIS en |-> (sineOrTriangle ==
    ($signed({{LOCAL_WIDTH{$past(signBitD1)} } ^ {1'b0, $past(halfSineOrTriangle)}}) + $signed({1'b0,$past(signBitD1)}))));

  // unscaledSignal selection
  assert property (@(posedge clk) `DIS en && (waveType==2'd0) |-> (unscaledSignal == $past(sineOrTriangle))); // SINE
  assert property (@(posedge clk) `DIS en && (waveType==2'd1) |-> (unscaledSignal == $past(sineOrTriangle))); // TRIANGLE
  assert property (@(posedge clk) `DIS en && (waveType==2'd2) |-> // SQUARE
    (unscaledSignal == $signed({$past(phase[FREQ_WIDTH-1]), {(LOCAL_WIDTH-2){~$past(phase[FREQ_WIDTH-1])}}, 1'b1})));
  generate
    if (FREQ_WIDTH >= LOCAL_WIDTH) begin
      assert property (@(posedge clk) `DIS en && (waveType==2'd3) |-> // SAWTOOTH
        (unscaledSignal == ($signed($past(phase)) >>> (FREQ_WIDTH-LOCAL_WIDTH))));
    end else begin
      assert property (@(posedge clk) `DIS en && (waveType==2'd3) |->
        (unscaledSignal == ($signed($past(phase)) <<< (LOCAL_WIDTH-FREQ_WIDTH))));
    end
  endgenerate

  // Multiply-accumulate path
  generate
    if (BIT_COMPRESS_OUTPUT) begin
      assert property (@(posedge clk) `DIS en |-> (wideSignalWord ==
        ($past(unscaledSignal) * $signed({1'b0, amplitude})
        + $signed({offset, $past(wideSignalWord[LOCAL_WIDTH-1:0])}))));
    end else begin
      assert property (@(posedge clk) `DIS en |-> (wideSignalWord ==
        ($past(unscaledSignal) * $signed({1'b0, amplitude})
        + $signed({offset, {LOCAL_WIDTH{1'b0}}}))));
    end
  endgenerate

  // Clamping
  assert property (@(posedge clk) `DIS en |-> (clampedSignal ==
    ((!(& $past(wideSignalWord[WIDE_WIDTH+1-:3]) | ~|$past(wideSignalWord[WIDE_WIDTH+1-:3])))
      ? { $past(wideSignalWord[WIDE_WIDTH+1]), {(OUT_WIDTH-1){~$past(wideSignalWord[WIDE_WIDTH+1])}} }
      :  $past(wideSignalWord[WIDE_WIDTH-1-:OUT_WIDTH]))));

  // Output selection
  generate
    if (INCLUDE_CLAMP) begin
      assert property (@(posedge clk) (outSignal == clampedSignal));
    end else begin
      assert property (@(posedge clk) (outSignal == wideSignalWord[WIDE_WIDTH-1-:OUT_WIDTH]));
    end
  endgenerate

  // Coverage
  cover property (@(posedge clk) `DIS en && waveType==2'd0); // SINE
  cover property (@(posedge clk) `DIS en && waveType==2'd1); // TRIANGLE
  cover property (@(posedge clk) `DIS en && waveType==2'd2); // SQUARE
  cover property (@(posedge clk) `DIS en && waveType==2'd3); // SAW
  cover property (@(posedge clk) `DIS en && !(&wideSignalWord[WIDE_WIDTH+1-:3] | ~|wideSignalWord[WIDE_WIDTH+1-:3])); // clamp saturates
  cover property (@(posedge clk) `DIS en &&  (&wideSignalWord[WIDE_WIDTH+1-:3] | ~|wideSignalWord[WIDE_WIDTH+1-:3])); // pass-through
  cover property (@(posedge clk) `DIS $rose(rst)); // reset exercised
  cover property (@(posedge clk) `DIS en && signBit != $past(signBit)); // sign toggles

endmodule

// Bind into all functionGen instances
bind functionGen functionGen_sva #(
  .ARCH(ARCH),
  .BIT_COMPRESS_PHASE(BIT_COMPRESS_PHASE),
  .BIT_COMPRESS_OUTPUT(BIT_COMPRESS_OUTPUT),
  .OUT_WIDTH(OUT_WIDTH),
  .FREQ_WIDTH(FREQ_WIDTH),
  .INCLUDE_CLAMP(INCLUDE_CLAMP)
) functionGen_sva_i();