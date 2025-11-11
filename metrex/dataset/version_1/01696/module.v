

module controllerHdl_Phase_Voltages_To_Compare_Values
          (
           V_0,
           V_1,
           V_2,
           C_0,
           C_1,
           C_2
          );


  input   signed [19:0] V_0;  input   signed [19:0] V_1;  input   signed [19:0] V_2;  output  [15:0] C_0;  output  [15:0] C_1;  output  [15:0] C_2;  wire signed [19:0] V [0:2];  wire signed [19:0] Half_Bus_Voltage_out1;  wire signed [20:0] Add2_v;  wire signed [20:0] Add2_add_cast;  wire signed [20:0] Add2_add_temp;  wire signed [20:0] Add2_add_cast_1;  wire signed [20:0] Add2_add_temp_1;  wire signed [20:0] Add2_add_cast_2;  wire signed [20:0] Add2_add_temp_2;  wire signed [19:0] Add2_out1 [0:2];  wire signed [39:0] Voltage_To_PWM_Compare_Units_out1 [0:2];  wire signed [39:0] Saturation1_out1 [0:2];  wire [15:0] pwm_compare [0:2];  assign V[0] = V_0;
  assign V[1] = V_1;
  assign V[2] = V_2;

  assign Half_Bus_Voltage_out1 = 20'sb00000110000000000000;



  assign Add2_v = Half_Bus_Voltage_out1;
  assign Add2_add_cast = V[0];
  assign Add2_add_temp = Add2_add_cast + Add2_v;
  assign Add2_out1[0] = Add2_add_temp[19:0];
  assign Add2_add_cast_1 = V[1];
  assign Add2_add_temp_1 = Add2_add_cast_1 + Add2_v;
  assign Add2_out1[1] = Add2_add_temp_1[19:0];
  assign Add2_add_cast_2 = V[2];
  assign Add2_add_temp_2 = Add2_add_cast_2 + Add2_v;
  assign Add2_out1[2] = Add2_add_temp_2[19:0];



  assign Voltage_To_PWM_Compare_Units_out1[0] = 341333 * Add2_out1[0];
  assign Voltage_To_PWM_Compare_Units_out1[1] = 341333 * Add2_out1[1];
  assign Voltage_To_PWM_Compare_Units_out1[2] = 341333 * Add2_out1[2];



  assign Saturation1_out1[0] = (Voltage_To_PWM_Compare_Units_out1[0] > 40'sh03E8000000 ? 40'sh03E8000000 :
              (Voltage_To_PWM_Compare_Units_out1[0] < 40'sh0000000000 ? 40'sh0000000000 :
              Voltage_To_PWM_Compare_Units_out1[0]));
  assign Saturation1_out1[1] = (Voltage_To_PWM_Compare_Units_out1[1] > 40'sh03E8000000 ? 40'sh03E8000000 :
              (Voltage_To_PWM_Compare_Units_out1[1] < 40'sh0000000000 ? 40'sh0000000000 :
              Voltage_To_PWM_Compare_Units_out1[1]));
  assign Saturation1_out1[2] = (Voltage_To_PWM_Compare_Units_out1[2] > 40'sh03E8000000 ? 40'sh03E8000000 :
              (Voltage_To_PWM_Compare_Units_out1[2] < 40'sh0000000000 ? 40'sh0000000000 :
              Voltage_To_PWM_Compare_Units_out1[2]));



  assign pwm_compare[0] = Saturation1_out1[0][39:24];
  assign pwm_compare[1] = Saturation1_out1[1][39:24];
  assign pwm_compare[2] = Saturation1_out1[2][39:24];



  assign C_0 = pwm_compare[0];

  assign C_1 = pwm_compare[1];

  assign C_2 = pwm_compare[2];

endmodule  