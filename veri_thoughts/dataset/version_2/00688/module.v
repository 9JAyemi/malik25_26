
module my_module(
   input                sgmii_refclk_p,
   input                sgmii_refclk_n,
   input [3:0]          sgmii_rxn,
   input [3:0]          sgmii_rxp,
   input                pl_btn,
   output [3:0]         sgmii_txn,
   output [3:0]         sgmii_txp,
   output               mdio_mdc,
   output [1:0]         pl_led,
   output [1:0]         pl_pmod
);


   reg [23:0] cnt_0;
   reg [23:0] cnt_1;
   reg [23:0] cnt_2;
   reg [23:0] cnt_3;

   always @(posedge sgmii_refclk_p) begin
     cnt_0 <= cnt_0 + 1'b1;
   end
   always @(posedge sgmii_refclk_p) begin
     cnt_1 <= cnt_1 + 1'b1;
   end
   always @(posedge sgmii_refclk_p) begin
     cnt_2 <= cnt_2 + 1'b1;
   end
   always @(posedge sgmii_refclk_p) begin
     cnt_3 <= cnt_3 + 1'b1;
   end


   assign pl_led[0]  = cnt_0[23];
   assign pl_led[1]  = cnt_1[23];
   assign pl_pmod[0] = cnt_3[23];
   assign pl_pmod[1] = pl_btn;

   assign sgmii_txn = sgmii_rxn ^ 4'b1111;
   assign sgmii_txp = sgmii_rxp ^ 4'b1111;

   assign mdio_mdc = pl_btn;

endmodule