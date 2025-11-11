// SVA for controllerHdl_ADC_Peripheral_To_Phase_Current
// Bind into DUT; clockless (combinational) assertions and covers

module controllerHdl_ADC_Peripheral_To_Phase_Current_sva;

  default clocking cb @(*); endclocking

  // Helper: 38->18 signed saturation per DUT logic
  function automatic signed [17:0] sat18_from38 (input signed [37:0] prod);
    automatic signed [17:0] MAXP = 18'sb011111111111111111;
    automatic signed [17:0] MINN = 18'sb100000000000000000;
    if (!prod[37] && (prod[36:34] != 3'b000)) return MAXP;
    else if (prod[37] && (prod[36:34] != 3'b111)) return MINN;
    else return $signed(prod[34:17]);
  endfunction

  // Constants and structure
  a_const_zero_offset: assert property (ADC_Zero_Offset_out1 == 18'sb0);
  a_const_gain:        assert property (ADC_Amps_Per_Driver_Unit_out1 == 18'sb010100000000000000);
  a_addv_def:          assert property (Add_v == $signed({ADC_Zero_Offset_out1[17], ADC_Zero_Offset_out1, 1'b0}));

  // Wiring correctness
  a_adc_map0: assert property (adc[0] == adc_0);
  a_adc_map1: assert property (adc[1] == adc_1);
  a_out_map0: assert property (phase_currents_0 == phase_currents[0]);
  a_out_map1: assert property (phase_currents_1 == phase_currents[1]);

  // Offset subtraction (and zero-offset implication)
  a_add0: assert property (Add_out1[0] == ($signed({{2{adc[0][17]}}, adc[0]}) - $signed(Add_v)));
  a_add1: assert property (Add_out1[1] == ($signed({{2{adc[1][17]}}, adc[1]}) - $signed(Add_v)));
  a_addv_zero_when_zero_offset: assert property ((ADC_Zero_Offset_out1==18'sd0) |-> (Add_v==20'sd0));

  // Multiply correctness
  a_mul0: assert property (Product_mul_temp   == $signed(Add_out1[0]) * $signed(ADC_Amps_Per_Driver_Unit_out1));
  a_mul1: assert property (Product_mul_temp_1 == $signed(Add_out1[1]) * $signed(ADC_Amps_Per_Driver_Unit_out1));

  // Saturation/output correctness
  a_sat0: assert property (phase_currents[0] == sat18_from38(Product_mul_temp));
  a_sat1: assert property (phase_currents[1] == sat18_from38(Product_mul_temp_1));

  // Pass-through when no overflow
  a_nosat0: assert property ((Product_mul_temp[36:34] == {3{Product_mul_temp[37]}}) |-> (phase_currents[0] == $signed(Product_mul_temp[34:17])));
  a_nosat1: assert property ((Product_mul_temp_1[36:34] == {3{Product_mul_temp_1[37]}}) |-> (phase_currents[1] == $signed(Product_mul_temp_1[34:17])));

  // No-X on key outputs
  a_no_x_out0: assert property (!$isunknown(phase_currents_0));
  a_no_x_out1: assert property (!$isunknown(phase_currents_1));

  // Coverage: sat+/sat-/no-sat for each channel, plus basic scenarios
  c_possat0: cover property (!Product_mul_temp[37] && (Product_mul_temp[36:34] != 3'b000) && (phase_currents[0] == 18'sb011111111111111111));
  c_negsat0: cover property ( Product_mul_temp[37] && (Product_mul_temp[36:34] != 3'b111) && (phase_currents[0] == 18'sb100000000000000000));
  c_nosat0:  cover property ( Product_mul_temp[36:34] == {3{Product_mul_temp[37]}} );

  c_possat1: cover property (!Product_mul_temp_1[37] && (Product_mul_temp_1[36:34] != 3'b000) && (phase_currents[1] == 18'sb011111111111111111));
  c_negsat1: cover property ( Product_mul_temp_1[37] && (Product_mul_temp_1[36:34] != 3'b111) && (phase_currents[1] == 18'sb100000000000000000));
  c_nosat1:  cover property ( Product_mul_temp_1[36:34] == {3{Product_mul_temp_1[37]}} );

  c_zero_in: cover property ((adc_0==18'sd0) && (adc_1==18'sd0) && (phase_currents_0==18'sd0) && (phase_currents_1==18'sd0));
  c_max_in0: cover property (adc_0==18'sb011111111111111111);
  c_min_in0: cover property (adc_0==18'sb100000000000000000);
  c_max_in1: cover property (adc_1==18'sb011111111111111111);
  c_min_in1: cover property (adc_1==18'sb100000000000000000);

endmodule

bind controllerHdl_ADC_Peripheral_To_Phase_Current controllerHdl_ADC_Peripheral_To_Phase_Current_sva sva_inst();