module DemoInterconnect_jtag_axi_0_0_wr_status_flags_as
   (out,
    \gic0.gc0.count_d1_reg[5] ,
    s_dclk_o);
  output out;
  input \gic0.gc0.count_d1_reg[5] ;
  input s_dclk_o;

  wire \gic0.gc0.count_d1_reg[5] ;
   wire ram_full_fb_i;
   wire ram_full_i;
  wire s_dclk_o;

  assign out = ram_full_fb_i;
   
   
   
  FDRE #(
    .INIT(1'b0)) 
    ram_full_fb_i_reg
       (.C(s_dclk_o),
        .CE(1'b1),
        .D(\gic0.gc0.count_d1_reg[5] ),
        .Q(ram_full_fb_i),
        .R(1'b0));
   
   
   
  FDRE #(
    .INIT(1'b0)) 
    ram_full_i_reg
       (.C(s_dclk_o),
        .CE(1'b1),
        .D(\gic0.gc0.count_d1_reg[5] ),
        .Q(ram_full_i),
        .R(1'b0));
endmodule

 
module FDRE 
  #(parameter INIT = 0) 
  (Q, D, C, CE, R);
  output Q;
  input D, C, CE, R;
  reg Q;

  always @(posedge C) begin
    if (R) begin
      Q <= INIT;
    end
    else if (CE) begin
      Q <= D;
    end
  end
endmodule