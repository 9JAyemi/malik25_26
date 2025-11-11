module system_auto_cc_0_synchronizer_ff__parameterized2 (
  output [3:0] D,
  input [3:0] Q_reg_reg_0,
  input s_aclk,
  input [0:0] ngwrdrst_grst_g7serrst_rd_rst_reg_reg_1
);

  wire [3:0] Q_reg;
  
  assign D = Q_reg;
  
  // Instantiate the four FDCE flip-flops
  FDCE  flipflop0 (
        .C(s_aclk),
        .CE(1'b1),
        .CLR(ngwrdrst_grst_g7serrst_rd_rst_reg_reg_1),
        .D(Q_reg_reg_0[0]),
        .Q(Q_reg[0])
  );
  
  FDCE flipflop1 (
        .C(s_aclk),
        .CE(1'b1),
        .CLR(ngwrdrst_grst_g7serrst_rd_rst_reg_reg_1),
        .D(Q_reg_reg_0[1]),
        .Q(Q_reg[1])
  );
  
  FDCE flipflop2 (
        .C(s_aclk),
        .CE(1'b1),
        .CLR(ngwrdrst_grst_g7serrst_rd_rst_reg_reg_1),
        .D(Q_reg_reg_0[2]),
        .Q(Q_reg[2])
  );
  
  FDCE flipflop3 (
        .C(s_aclk),
        .CE(1'b1),
        .CLR(ngwrdrst_grst_g7serrst_rd_rst_reg_reg_1),
        .D(Q_reg_reg_0[3]),
        .Q(Q_reg[3])
  );

endmodule

module FDCE (
  input C,
  input CE,
  input CLR,
  input D,
  output reg Q
);

  always @(posedge C or posedge CLR)
    if (CLR)
      Q <= 1'b0;
    else if (CE)
      Q <= D;

endmodule