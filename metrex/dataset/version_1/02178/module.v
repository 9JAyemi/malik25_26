module Inverse_Clarke_Transform (
    input signed [17:0] alpha_voltage,
    input signed [17:0] beta_voltage,
    output signed [17:0] phase_voltages_0,
    output signed [17:0] phase_voltages_1,
    output signed [17:0] phase_voltages_2
);

    wire signed [35:0] voltage_phase_a;
    wire signed [35:0] Gain1_out1;
    wire signed [35:0] Gain_out1;
    wire signed [35:0] voltage_phase_b;
    wire signed [37:0] Add1_cast;
    wire signed [37:0] Add1_cast_1;
    wire signed [37:0] Add1_sub_cast;
    wire signed [37:0] Add1_sub_temp;
    wire signed [35:0] voltage_phase_c;
    wire signed [35:0] Mux_out1 [0:2];
    wire signed [17:0] Current_Data_Type_out1 [0:2];

    assign voltage_phase_a = {{2{alpha_voltage[17]}}, {alpha_voltage, 16'b0000000000000000}};
    assign Gain1_out1 = 56756 * beta_voltage;
    assign Gain_out1 = {{3{alpha_voltage[17]}}, {alpha_voltage, 15'b000000000000000}};
    assign voltage_phase_b = Gain1_out1 - Gain_out1;
    assign Add1_cast = Gain_out1;
    assign Add1_cast_1 =  - (Add1_cast);
    assign Add1_sub_cast = Gain1_out1;
    assign Add1_sub_temp = Add1_cast_1 - Add1_sub_cast;
    assign voltage_phase_c = Add1_sub_temp[35:0];
    assign Mux_out1[0] = voltage_phase_a;
    assign Mux_out1[1] = voltage_phase_b;
    assign Mux_out1[2] = voltage_phase_c;

    assign Current_Data_Type_out1[0] = ((Mux_out1[0][35] == 1'b0) && (Mux_out1[0][34:30] != 5'b00000) ? 18'sb011111111111111111 :
              ((Mux_out1[0][35] == 1'b1) && (Mux_out1[0][34:30] != 5'b11111) ? 18'sb100000000000000000 :
              $signed(Mux_out1[0][30:13])));
    assign Current_Data_Type_out1[1] = ((Mux_out1[1][35] == 1'b0) && (Mux_out1[1][34:30] != 5'b00000) ? 18'sb011111111111111111 :
              ((Mux_out1[1][35] == 1'b1) && (Mux_out1[1][34:30] != 5'b11111) ? 18'sb100000000000000000 :
              $signed(Mux_out1[1][30:13])));
    assign Current_Data_Type_out1[2] = ((Mux_out1[2][35] == 1'b0) && (Mux_out1[2][34:30] != 5'b00000) ? 18'sb011111111111111111 :
              ((Mux_out1[2][35] == 1'b1) && (Mux_out1[2][34:30] != 5'b11111) ? 18'sb100000000000000000 :
              $signed(Mux_out1[2][30:13])));

    assign phase_voltages_0 = Current_Data_Type_out1[0];
    assign phase_voltages_1 = Current_Data_Type_out1[1];
    assign phase_voltages_2 = Current_Data_Type_out1[2];

endmodule