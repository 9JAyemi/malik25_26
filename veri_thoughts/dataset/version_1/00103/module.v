module ByteMuxOct (
  
  input[7:0] A_i,
  
  input[7:0] B_i,
  
  input[7:0] C_i,
  
  input[7:0] D_i,
  
  input[7:0] E_i,
  
  input[7:0] F_i,
  
  input[7:0] G_i,
  
  input[7:0] H_i,
  
  input SAB_i,
  
  input SC_i,
  
  input SD_i,
  
  input SE_i,
  
  input SF_i,
  
  input SG_i,
  
  input SH_i,
  
  output[7:0] Y_o
);

wire [7:0] AB      = SAB_i ? B_i : A_i;
wire [7:0] ABC     = SC_i  ? C_i : AB;
wire [7:0] ABCD    = SD_i  ? D_i : ABC;
wire [7:0] ABCDE   = SE_i  ? E_i : ABCD;
wire [7:0] ABCDEF  = SF_i  ? F_i : ABCDE;
wire [7:0] ABCDEFG = SG_i  ? G_i : ABCDEF;
assign     Y_o     = SH_i  ? H_i : ABCDEFG;

endmodule
