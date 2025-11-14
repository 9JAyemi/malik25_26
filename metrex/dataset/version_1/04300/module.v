module adder_with_carry(
  input clk,
  input reset,
  input [15:0] A,
  input [15:0] B,
  input cin,
  input [3:0] sel,
  output [15:0] sum,
  output cout
);

  // Barrel shifter
  wire [15:0] shifted_A;
  wire [15:0] shifted_B;
  
  assign shifted_A = (sel == 0) ? A :
                     (sel == 1) ? {A[14:0], 16'b0} :
                     (sel == 2) ? {A[13:0], 16'b0, 16'b0} :
                     (sel == 3) ? {A[12:0], 16'b0, 16'b0, 16'b0} :
                     (sel == 4) ? {A[11:0], 16'b0, 16'b0, 16'b0, 16'b0} :
                     (sel == 5) ? {A[10:0], 16'b0, 16'b0, 16'b0, 16'b0, 16'b0} :
                     (sel == 6) ? {A[9:0], 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0} :
                     (sel == 7) ? {A[8:0], 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0} :
                     (sel == 8) ? {A[7:0], 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0} :
                     (sel == 9) ? {A[6:0], 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0} :
                     (sel == 10) ? {A[5:0], 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0} :
                     (sel == 11) ? {A[4:0], 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0} :
                     (sel == 12) ? {A[3:0], 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0} :
                     (sel == 13) ? {A[2:0], 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0} :
                     (sel == 14) ? {A[1:0], 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0} :
                                   {A[0], 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0};
  
  assign shifted_B = (sel == 0) ? B :
                     (sel == 1) ? {B[14:0], 16'b0} :
                     (sel == 2) ? {B[13:0], 16'b0, 16'b0} :
                     (sel == 3) ? {B[12:0], 16'b0, 16'b0, 16'b0} :
                     (sel == 4) ? {B[11:0], 16'b0, 16'b0, 16'b0, 16'b0} :
                     (sel == 5) ? {B[10:0], 16'b0, 16'b0, 16'b0, 16'b0, 16'b0} :
                     (sel == 6) ? {B[9:0], 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0} :
                     (sel == 7) ? {B[8:0], 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0} :
                     (sel == 8) ? {B[7:0], 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0} :
                     (sel == 9) ? {B[6:0], 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0} :
                     (sel == 10) ? {B[5:0], 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0} :
                     (sel == 11) ? {B[4:0], 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0} :
                     (sel == 12) ? {B[3:0], 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0} :
                     (sel == 13) ? {B[2:0], 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0} :
                     (sel == 14) ? {B[1:0], 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0} :
                                   {B[0], 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0, 16'b0};
  
  // Multiplexer
  wire [15:0] selected_input;
  
  assign selected_input = (sel == 0) ? shifted_A :
                          (sel == 1) ? {shifted_A[14:0], shifted_B[0]} :
                          (sel == 2) ? {shifted_A[13:0], shifted_B[1:0]} :
                          (sel == 3) ? {shifted_A[12:0], shifted_B[2:0]} :
                          (sel == 4) ? {shifted_A[11:0], shifted_B[3:0]} :
                          (sel == 5) ? {shifted_A[10:0], shifted_B[4:0]} :
                          (sel == 6) ? {shifted_A[9:0], shifted_B[5:0]} :
                          (sel == 7) ? {shifted_A[8:0], shifted_B[6:0]} :
                          (sel == 8) ? {shifted_A[7:0], shifted_B[7:0]} :
                          (sel == 9) ? {shifted_A[6:0], shifted_B[8:0]} :
                          (sel == 10) ? {shifted_A[5:0], shifted_B[9:0]} :
                          (sel == 11) ? {shifted_A[4:0], shifted_B[10:0]} :
                          (sel == 12) ? {shifted_A[3:0], shifted_B[11:0]} :
                          (sel == 13) ? {shifted_A[2:0], shifted_B[12:0]} :
                          (sel == 14) ? {shifted_A[1:0], shifted_B[13:0]} :
                                        {shifted_A[0], shifted_B[14:0]};
  
  // Full adder
  wire [15:0] temp_sum;
  wire temp_cout;
  
  assign {temp_cout, temp_sum} = shifted_A + shifted_B + cin;
  
  // Output
  assign sum = selected_input + temp_sum;
  assign cout = temp_cout;

endmodule