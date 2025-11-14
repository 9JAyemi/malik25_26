module pcieInterface(
  input  wire        sys_clkp,     // System Clock +
  input  wire        sys_clkn,     // System Clock -
  input  wire        pci_clkp,     // PCIe Clock +
  input  wire        pci_clkn,     // PCIe Clock -
  input  wire        pci_reset_n,  // PCIe Reset
  input  wire [7:0]  pci_rxp,      // PCIe receive lane positive
  input  wire [7:0]  pci_rxn,      // PCIe receive lane negative
  input  wire        pps_in,      // PPS input signal
  output wire [7:0]  pci_txp,     // PCIe transmit lane positive
  output wire [7:0]  pci_txn,     // PCIe transmit lane negative
  output wire [2:0]  led,         // LED control signal
  output wire        pps_out      // PPS output signal
);

reg [7:0] pci_txp_reg;
reg [7:0] pci_txn_reg;
reg [2:0] led_reg;
reg        pps_out_reg;

always @(posedge sys_clkp) begin
  // PPS output signal is synchronized to the system clock
  pps_out_reg <= pps_in;
end

always @(posedge pci_clkp) begin
  if (!pci_reset_n) begin
    // Reset all output signals
    pci_txp_reg <= 8'b0;
    pci_txn_reg <= 8'b0;
    led_reg <= 3'b0;
  end else begin
    // Transmit received data
    pci_txp_reg <= pci_rxp;
    pci_txn_reg <= pci_rxn;
    
    // Control LEDs based on received data
    case (pci_rxp[2:0])
      3'b000: led_reg <= 3'b000;
      3'b001: led_reg <= 3'b001;
      3'b010: led_reg <= 3'b010;
      3'b011: led_reg <= 3'b011;
      3'b100: led_reg <= 3'b100;
      3'b101: led_reg <= 3'b101;
      3'b110: led_reg <= 3'b110;
      3'b111: led_reg <= 3'b111;
    endcase
  end
end

assign pci_txp = pci_txp_reg;
assign pci_txn = pci_txn_reg;
assign led = led_reg;
assign pps_out = pps_out_reg;

endmodule