

module controllerHdl_Wrap_2pi
          (
           x,
           wrap
          );


  input   signed [18:0] x;  output  signed [17:0] wrap;  wire signed [18:0] Two_Pi1_out1;  wire signed [18:0] Two_Pi3_out1;  wire Relational_Operator1_relop1;
  wire signed [19:0] x_dtc;  wire signed [18:0] Two_Pi2_out1;  wire signed [18:0] Two_Pi_out1;  wire Relational_Operator_relop1;
  wire signed [19:0] Add2_add_cast;  wire signed [19:0] Add2_add_cast_1;  wire signed [19:0] Add2_out1;  wire signed [19:0] Switch1_out1;  wire signed [17:0] Switch1_out1_dtc;  wire signed [19:0] Add1_sub_cast;  wire signed [19:0] Add1_sub_cast_1;  wire signed [19:0] Add1_out1;  wire signed [17:0] Add1_out1_dtc;  wire signed [17:0] Switch_out1;  assign Two_Pi1_out1 = 19'sb0011001001000100000;



  assign Two_Pi3_out1 = 19'sb0000000000000000000;



  assign Relational_Operator1_relop1 = (x < Two_Pi3_out1 ? 1'b1 :
              1'b0);



  assign x_dtc = x;



  assign Two_Pi2_out1 = 19'sb0011001001000100000;



  assign Two_Pi_out1 = 19'sb0011001001000100000;



  assign Relational_Operator_relop1 = (x >= Two_Pi1_out1 ? 1'b1 :
              1'b0);



  assign Add2_add_cast = x;
  assign Add2_add_cast_1 = Two_Pi2_out1;
  assign Add2_out1 = Add2_add_cast + Add2_add_cast_1;



  assign Switch1_out1 = (Relational_Operator1_relop1 == 1'b0 ? x_dtc :
              Add2_out1);



  assign Switch1_out1_dtc = Switch1_out1[17:0];



  assign Add1_sub_cast = x;
  assign Add1_sub_cast_1 = Two_Pi_out1;
  assign Add1_out1 = Add1_sub_cast - Add1_sub_cast_1;



  assign Add1_out1_dtc = Add1_out1[17:0];



  assign Switch_out1 = (Relational_Operator_relop1 == 1'b0 ? Switch1_out1_dtc :
              Add1_out1_dtc);



  assign wrap = Switch_out1;

endmodule  