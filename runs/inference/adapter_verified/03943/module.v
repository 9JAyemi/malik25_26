
module system_axi_ethernetlite_0_0_synchronizer_ff_9
(
  AS,
  out,
  phy_tx_clk,
  in0
);

output [0:0] AS;
input  out;
input  phy_tx_clk;
input  [0:0] in0;

reg Q_reg;

always @(posedge phy_tx_clk) begin
  Q_reg <= out;
end

assign AS = (in0 & ~Q_reg);

endmodule
