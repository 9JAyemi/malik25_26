
module ddr_interface(
   inout [14:0]         DDR_addr,
   inout [2:0]          DDR_ba,
   inout                DDR_cas_n,
   inout                DDR_ck_n,
   inout                DDR_ck_p,
   inout                DDR_cke,
   inout                DDR_cs_n,
   inout [3:0]          DDR_dm,
   inout [31:0]         DDR_dq,
   inout [3:0]          DDR_dqs_n,
   inout [3:0]          DDR_dqs_p,
   inout                DDR_odt,
   inout                DDR_ras_n,
   inout                DDR_reset_n,
   inout                DDR_we_n,
   inout                FIXED_IO_ddr_vrn,
   inout                FIXED_IO_ddr_vrp,
   inout [53:0]         FIXED_IO_mio,
   inout                FIXED_IO_ps_clk,
   inout                FIXED_IO_ps_porb,
   inout                FIXED_IO_ps_srstb,

   input                PL_SGMII_REFCLK_125M_P,
   input                PL_SGMII_REFCLK_125M_N,

   output reg [1:0]     pl_led      ,
   output reg [1:0]     pl_pmod
);

   reg [23:0] cnt_0;
   reg [24:0] cnt_1;
   reg [24:0] cnt_2;
   reg [23:0] cnt_3;

   always @(posedge FIXED_IO_ps_clk) begin
     if (cnt_0 == 24'd8388607) cnt_0 <= 0;
     else cnt_0 <= cnt_0 + 1'b1;
   end
   always @(posedge FIXED_IO_ps_clk) begin
     if (cnt_1 == 25'd16777215) cnt_1 <= 0;
     else cnt_1 <= cnt_1 + 1'b1;
   end
   always @(posedge FIXED_IO_ps_clk) begin
     if (cnt_2 == 25'd33554431) cnt_2 <= 0;
     else cnt_2 <= cnt_2 + 1'b1;
   end
   always @(posedge PL_SGMII_REFCLK_125M_P) begin
     if (cnt_3 == 24'd16777215) cnt_3 <= 0;
     else cnt_3 <= cnt_3 + 1'b1;
   end

   always @(cnt_0) begin
     pl_led[0] = cnt_0[23];
   end
   always @(cnt_1) begin
     pl_led[1] = cnt_1[24];
   end
   always @(cnt_2) begin
     pl_pmod[0] = cnt_2[24];
   end
   always @(cnt_3) begin
     pl_pmod[1] = cnt_3[23];
   end

endmodule