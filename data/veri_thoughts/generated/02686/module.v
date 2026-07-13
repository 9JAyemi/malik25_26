
module Add_Subt ( clk, rst, load_i, Add_Sub_op_i, Data_A_i, PreData_B_i, 
        Data_Result_o, FSM_C_o);
  input [25:0] Data_A_i;
  input [25:0] PreData_B_i;
  output [25:0] Data_Result_o;
  input clk, rst, load_i, Add_Sub_op_i;
  output FSM_C_o;

  wire   [26:0] S_to_D;

  // Perform addition or subtraction based on Add_Sub_op_i
  assign S_to_D = (Add_Sub_op_i) ? (Data_A_i - PreData_B_i) : (Data_A_i + PreData_B_i);
  
  // Store the result of the addition or subtraction in Data_Result_o
  RegisterAdd_W26 Add_Subt_Result ( .clk(clk), .rst(rst), .load(load_i), .D(
        S_to_D[25:0]), .Q(Data_Result_o) );
  
  // Detect overflow and set FSM_C_o high if overflow occurs
  RegisterAdd_W1 Add_overflow_Result ( .clk(clk), .rst(rst), .load(load_i), 
        .D(S_to_D[26]), .Q(FSM_C_o) );
  
endmodule
module RegisterAdd_W26 ( clk, rst, load, D, Q );
  input                   clk, rst, load;
  input  [25:0]           D;
  output [25:0]           Q;
  reg    [25:0]           Q;
  always@(posedge clk)
    if (rst)
      Q <= 0;
    else if (load)
      Q <= D;
endmodule
module RegisterAdd_W1 ( clk, rst, load, D, Q );
  input                   clk, rst, load;
  input                    D;
  output reg               Q;
  always@(posedge clk)
    if (rst)
      Q <= 0;
    else if (load)
      Q <= D;
endmodule