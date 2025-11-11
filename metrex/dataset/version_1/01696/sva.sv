// SVA for controllerHdl_Phase_Voltages_To_Compare_Values
// Concise, comprehensive checks and coverage; bind to DUT and use immediate assertions for combinational logic.

bind controllerHdl_Phase_Voltages_To_Compare_Values controllerHdl_Phase_Voltages_To_Compare_Values_sva();

module controllerHdl_Phase_Voltages_To_Compare_Values_sva;

  // Constants
  localparam signed [19:0] HALF = 20'sb00000110000000000000;
  localparam signed [39:0] MAX40 = 40'sh03E8000000;

  // Basic sanity: no X on IOs
  always_comb begin
    assert (!$isunknown({V_0,V_1,V_2})) else $error("Inputs contain X/Z");
    assert (!$isunknown({C_0,C_1,C_2})) else $error("Outputs contain X/Z");
  end

  // Structural equivalence and arithmetic/path checks
  always_comb begin
    // Constant
    assert (Half_Bus_Voltage_out1 === HALF) else $error("Half_Bus_Voltage_out1 mismatch");

    // Array mapping
    assert (V[0] === V_0 && V[1] === V_1 && V[2] === V_2) else $error("V array mapping mismatch");

    // Per-channel checks
    automatic int i;
    for (i = 0; i < 3; i++) begin
      // Addition with truncation
      assert (Add2_out1[i] === ( (V[i] + HALF) [19:0] ))
        else $error("Add2_out1[%0d] mismatch", i);

      // Multiplied, truncated to 40b
      assert (Voltage_To_PWM_Compare_Units_out1[i] ===
              ( $signed(32'sd341333) * $signed(Add2_out1[i]) )[39:0])
        else $error("Voltage_To_PWM_Compare_Units_out1[%0d] mismatch", i);

      // Saturation range
      assert (Saturation1_out1[i] >= 40'sd0 && Saturation1_out1[i] <= MAX40)
        else $error("Saturation1_out1[%0d] out of range", i);

      // Saturation functional behavior
      if ($signed(Voltage_To_PWM_Compare_Units_out1[i]) < 0)
        assert (Saturation1_out1[i] === 40'sd0)
          else $error("Saturation low clip failed [%0d]", i);
      else if ($signed(Voltage_To_PWM_Compare_Units_out1[i]) > $signed(MAX40))
        assert (Saturation1_out1[i] === MAX40)
          else $error("Saturation high clip failed [%0d]", i);
      else
        assert (Saturation1_out1[i] === Voltage_To_PWM_Compare_Units_out1[i])
          else $error("Saturation pass-through failed [%0d]", i);

      // PWM compare extraction
      assert (pwm_compare[i] === Saturation1_out1[i][39:24])
        else $error("pwm_compare[%0d] extraction mismatch", i);
    end

    // Output mapping
    assert (C_0 === pwm_compare[0]) else $error("C_0 mapping mismatch");
    assert (C_1 === pwm_compare[1]) else $error("C_1 mapping mismatch");
    assert (C_2 === pwm_compare[2]) else $error("C_2 mapping mismatch");

    // Output range [0..1000]
    assert (C_0 inside {[16'd0:16'd1000]}) else $error("C_0 out of range");
    assert (C_1 inside {[16'd0:16'd1000]}) else $error("C_1 out of range");
    assert (C_2 inside {[16'd0:16'd1000]}) else $error("C_2 out of range");

    // Functional mapping wrt pre-saturation value
    if ($signed(Voltage_To_PWM_Compare_Units_out1[0]) < 0)       assert (C_0 == 16'd0);
    else if ($signed(Voltage_To_PWM_Compare_Units_out1[0]) > $signed(MAX40)) assert (C_0 == 16'd1000);
    else                                                         assert (C_0 == Voltage_To_PWM_Compare_Units_out1[0][39:24]);

    if ($signed(Voltage_To_PWM_Compare_Units_out1[1]) < 0)       assert (C_1 == 16'd0);
    else if ($signed(Voltage_To_PWM_Compare_Units_out1[1]) > $signed(MAX40)) assert (C_1 == 16'd1000);
    else                                                         assert (C_1 == Voltage_To_PWM_Compare_Units_out1[1][39:24]);

    if ($signed(Voltage_To_PWM_Compare_Units_out1[2]) < 0)       assert (C_2 == 16'd0);
    else if ($signed(Voltage_To_PWM_Compare_Units_out1[2]) > $signed(MAX40)) assert (C_2 == 16'd1000);
    else                                                         assert (C_2 == Voltage_To_PWM_Compare_Units_out1[2][39:24]);
  end

  // Targeted coverage
  always_comb begin
    // Saturation mode coverage per channel
    automatic int i;
    for (i = 0; i < 3; i++) begin
      cover ($signed(Voltage_To_PWM_Compare_Units_out1[i]) < 0);
      cover ($signed(Voltage_To_PWM_Compare_Units_out1[i]) == 0);
      cover ($signed(Voltage_To_PWM_Compare_Units_out1[i]) > 0 &&
             $signed(Voltage_To_PWM_Compare_Units_out1[i]) < $signed(MAX40));
      cover ($signed(Voltage_To_PWM_Compare_Units_out1[i]) == $signed(MAX40));
      cover ($signed(Voltage_To_PWM_Compare_Units_out1[i]) >  $signed(MAX40));

      // Output edges
      cover (pwm_compare[i] == 16'd0);
      cover (pwm_compare[i] == 16'd1);
      cover (pwm_compare[i] == 16'd999);
      cover (pwm_compare[i] == 16'd1000);

      // Extreme input values
      cover (V[i] == 20'sh7FFFF);   // max positive
      cover (V[i] == -20'sh80000);  // max negative
    end
  end

endmodule