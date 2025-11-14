module etx_cfg (
   input reset,
   input clk,
   input mi_en,
   input mi_we,
   input [6:0] mi_addr,
   input [31:0] mi_din,
   input [15:0] tx_status,
   output [31:0] mi_dout,
   output tx_enable,
   output mmu_enable,
   output gpio_enable,
   output remap_enable,
   output [8:0] gpio_data,
   output [3:0] ctrlmode,
   output ctrlmode_bypass
);

   // Compile-time parameters
   parameter PW = 104;
   parameter RFAW = 6;
   parameter DEFAULT_VERSION = 16'h0000;

   // Registers
   reg [15:0] ecfg_version_reg;
   reg [10:0] ecfg_tx_config_reg;
   reg [8:0] ecfg_tx_gpio_reg;
   reg [2:0] ecfg_tx_status_reg;
   reg [31:0] mi_dout;
   reg ecfg_access;

   // Wires
   wire ecfg_read;
   wire ecfg_write;
   wire ecfg_version_write;
   wire ecfg_tx_config_write;
   wire ecfg_tx_gpio_write;
   wire ecfg_tx_status_write;
   wire loop_mode;

   // Address decode logic
   assign ecfg_write = mi_en & mi_we;
   assign ecfg_read = mi_en & ~mi_we;
   assign ecfg_version_write = ecfg_write & (mi_addr[6:2] == 5'b00000);
   assign ecfg_tx_config_write = ecfg_write & (mi_addr[6:2] == 5'b00010);
   assign ecfg_tx_status_write = ecfg_write & (mi_addr[6:2] == 5'b00011);
   assign ecfg_tx_gpio_write = ecfg_write & (mi_addr[6:2] == 5'b00100);

   // Version register
   always @(posedge clk) begin
      if (reset) begin
         ecfg_version_reg <= DEFAULT_VERSION;
      end else if (ecfg_version_write) begin
         ecfg_version_reg <= mi_din[15:0];
      end
   end

   // Configuration register
   always @(posedge clk) begin
      if (reset) begin
         ecfg_tx_config_reg <= 11'b0;
      end else if (ecfg_tx_config_write) begin
         ecfg_tx_config_reg <= mi_din[10:0];
      end
   end

   // Status register
   always @(posedge clk) begin
      if (reset) begin
         ecfg_tx_status_reg <= 3'b0;
      end else if (ecfg_tx_status_write) begin
         ecfg_tx_status_reg <= {3'b0, tx_status[2:0]};
      end
   end

   // GPIO data register
   always @(posedge clk) begin
      if (ecfg_tx_gpio_write) begin
         ecfg_tx_gpio_reg <= mi_din[8:0];
      end
   end

   // Data readback mux
   always @(posedge clk) begin
      if (ecfg_read) begin
         case (mi_addr[6:2])
            5'b00000: mi_dout <= {16'b0, ecfg_version_reg};
            5'b00010: mi_dout <= {21'b0, ecfg_tx_config_reg};
            5'b00011: mi_dout <= {16'b0, tx_status[15:3], ecfg_tx_status_reg};
            5'b00100: mi_dout <= {23'b0, ecfg_tx_gpio_reg};
            default: mi_dout <= 32'd0;
         endcase
      end else begin
         mi_dout <= 32'd0;
      end
   end

   // Control signals
   assign tx_enable = 1'b1;
   assign mmu_enable = ecfg_tx_config_reg[1];
   assign remap_enable = ecfg_tx_config_reg[3:2] == 2'b01;
   assign ctrlmode[3:0] = ecfg_tx_config_reg[7:4];
   assign ctrlmode_bypass = ecfg_tx_config_reg[8];
   assign gpio_enable = (ecfg_tx_config_reg[10:9] == 2'b01);
   assign gpio_data[8:0] = ecfg_tx_gpio_reg[8:0];

endmodule