`ifdef BSV_ASSIGNMENT_DELAY
`else
  `define BSV_ASSIGNMENT_DELAY
`endif

`ifdef BSV_POSITIVE_RESET
  `define BSV_RESET_VALUE 1'b1
  `define BSV_RESET_EDGE posedge
`else
  `define BSV_RESET_VALUE 1'b0
  `define BSV_RESET_EDGE negedge
`endif

module mkSoC_Map(CLK,
		 RST_N,

		 m_plic_addr_base,

		 m_plic_addr_size,

		 m_plic_addr_lim,

		 m_near_mem_io_addr_base,

		 m_near_mem_io_addr_size,

		 m_near_mem_io_addr_lim,

		 m_flash_mem_addr_base,

		 m_flash_mem_addr_size,

		 m_flash_mem_addr_lim,

		 m_ethernet_0_addr_base,

		 m_ethernet_0_addr_size,

		 m_ethernet_0_addr_lim,

		 m_dma_0_addr_base,

		 m_dma_0_addr_size,

		 m_dma_0_addr_lim,

		 m_uart16550_0_addr_base,

		 m_uart16550_0_addr_size,

		 m_uart16550_0_addr_lim,

		 m_gpio_0_addr_base,

		 m_gpio_0_addr_size,

		 m_gpio_0_addr_lim,

		 m_boot_rom_addr_base,

		 m_boot_rom_addr_size,

		 m_boot_rom_addr_lim,

		 m_ddr4_0_uncached_addr_base,

		 m_ddr4_0_uncached_addr_size,

		 m_ddr4_0_uncached_addr_lim,

		 m_ddr4_0_cached_addr_base,

		 m_ddr4_0_cached_addr_size,

		 m_ddr4_0_cached_addr_lim,

		 m_is_mem_addr_addr,
		 m_is_mem_addr,

		 m_is_IO_addr_addr,
		 m_is_IO_addr,

		 m_is_near_mem_IO_addr_addr,
		 m_is_near_mem_IO_addr,

		 m_pc_reset_value,

		 m_mtvec_reset_value,

		 m_nmivec_reset_value);
  input  CLK;
  input  RST_N;

  output [63 : 0] m_plic_addr_base;

  output [63 : 0] m_plic_addr_size;

  output [63 : 0] m_plic_addr_lim;

  output [63 : 0] m_near_mem_io_addr_base;

  output [63 : 0] m_near_mem_io_addr_size;

  output [63 : 0] m_near_mem_io_addr_lim;

  output [63 : 0] m_flash_mem_addr_base;

  output [63 : 0] m_flash_mem_addr_size;

  output [63 : 0] m_flash_mem_addr_lim;

  output [63 : 0] m_ethernet_0_addr_base;

  output [63 : 0] m_ethernet_0_addr_size;

  output [63 : 0] m_ethernet_0_addr_lim;

  output [63 : 0] m_dma_0_addr_base;

  output [63 : 0] m_dma_0_addr_size;

  output [63 : 0] m_dma_0_addr_lim;

  output [63 : 0] m_uart16550_0_addr_base;

  output [63 : 0] m_uart16550_0_addr_size;

  output [63 : 0] m_uart16550_0_addr_lim;

  output [63 : 0] m_gpio_0_addr_base;

  output [63 : 0] m_gpio_0_addr_size;

  output [63 : 0] m_gpio_0_addr_lim;

  output [63 : 0] m_boot_rom_addr_base;

  output [63 : 0] m_boot_rom_addr_size;

  output [63 : 0] m_boot_rom_addr_lim;

  output [63 : 0] m_ddr4_0_uncached_addr_base;

  output [63 : 0] m_ddr4_0_uncached_addr_size;

  output [63 : 0] m_ddr4_0_uncached_addr_lim;

  output [63 : 0] m_ddr4_0_cached_addr_base;

  output [63 : 0] m_ddr4_0_cached_addr_size;

  output [63 : 0] m_ddr4_0_cached_addr_lim;

  input  [63 : 0] m_is_mem_addr_addr;
  output m_is_mem_addr;

  input  [63 : 0] m_is_IO_addr_addr;
  output m_is_IO_addr;

  input  [63 : 0] m_is_near_mem_IO_addr_addr;
  output m_is_near_mem_IO_addr;

  output [63 : 0] m_pc_reset_value;

  output [63 : 0] m_mtvec_reset_value;

  output [63 : 0] m_nmivec_reset_value;

  wire [63 : 0] m_boot_rom_addr_base,
		m_boot_rom_addr_lim,
		m_boot_rom_addr_size,
		m_ddr4_0_cached_addr_base,
		m_ddr4_0_cached_addr_lim,
		m_ddr4_0_cached_addr_size,
		m_ddr4_0_uncached_addr_base,
		m_ddr4_0_uncached_addr_lim,
		m_ddr4_0_uncached_addr_size,
		m_dma_0_addr_base,
		m_dma_0_addr_lim,
		m_dma_0_addr_size,
		m_ethernet_0_addr_base,
		m_ethernet_0_addr_lim,
		m_ethernet_0_addr_size,
		m_flash_mem_addr_base,
		m_flash_mem_addr_lim,
		m_flash_mem_addr_size,
		m_gpio_0_addr_base,
		m_gpio_0_addr_lim,
		m_gpio_0_addr_size,
		m_mtvec_reset_value,
		m_near_mem_io_addr_base,
		m_near_mem_io_addr_lim,
		m_near_mem_io_addr_size,
		m_nmivec_reset_value,
		m_pc_reset_value,
		m_plic_addr_base,
		m_plic_addr_lim,
		m_plic_addr_size,
		m_uart16550_0_addr_base,
		m_uart16550_0_addr_lim,
		m_uart16550_0_addr_size;
  wire m_is_IO_addr, m_is_mem_addr, m_is_near_mem_IO_addr;

  wire NOT_m_is_IO_addr_addr_ULT_0xC000000_AND_m_is_I_ETC___d37,
       NOT_m_is_IO_addr_addr_ULT_0xC000000_AND_m_is_I_ETC___d82,
       m_is_IO_addr_addr_ULT_0x30000000___d80,
       m_is_IO_addr_addr_ULT_0x70000000___d35,
       m_is_IO_addr_addr_ULT_1073741824___d13;

  assign m_plic_addr_base = 64'h000000000C000000 ;

  assign m_plic_addr_size = 64'h0000000000400000 ;

  assign m_plic_addr_lim = 64'd205520896 ;

  assign m_near_mem_io_addr_base = 64'h0000000010000000 ;

  assign m_near_mem_io_addr_size = 64'h0000000000010000 ;

  assign m_near_mem_io_addr_lim = 64'd268500992 ;

  assign m_flash_mem_addr_base = 64'h0000000040000000 ;

  assign m_flash_mem_addr_size = 64'h0000000008000000 ;

  assign m_flash_mem_addr_lim = 64'd1207959552 ;

  assign m_ethernet_0_addr_base = 64'h0000000062100000 ;

  assign m_ethernet_0_addr_size = 64'h0000000000040000 ;

  assign m_ethernet_0_addr_lim = 64'd1645477888 ;

  assign m_dma_0_addr_base = 64'h0000000062200000 ;

  assign m_dma_0_addr_size = 64'h0000000000010000 ;

  assign m_dma_0_addr_lim = 64'd1646329856 ;

  assign m_uart16550_0_addr_base = 64'h0000000062300000 ;

  assign m_uart16550_0_addr_size = 64'h0000000000001000 ;

  assign m_uart16550_0_addr_lim = 64'd1647316992 ;

  assign m_gpio_0_addr_base = 64'h000000006FFF0000 ;

  assign m_gpio_0_addr_size = 64'h0000000000010000 ;

  assign m_gpio_0_addr_lim = 64'd1879048192 ;

  assign m_boot_rom_addr_base = 64'h0000000070000000 ;

  assign m_boot_rom_addr_size = 64'h0000000000001000 ;

  assign m_boot_rom_addr_lim = 64'd1879052288 ;

  assign m_ddr4_0_uncached_addr_base = 64'h0000000080000000 ;

  assign m_ddr4_0_uncached_addr_size = 64'h0000000040000000 ;

  assign m_ddr4_0_uncached_addr_lim = 64'h00000000C0000000 ;

  assign m_ddr4_0_cached_addr_base = 64'h00000000C0000000 ;

  assign m_ddr4_0_cached_addr_size = 64'h0000000040000000 ;

  assign m_ddr4_0_cached_addr_lim = 64'h0000000100000000 ;

  assign m_is_mem_addr =
	     m_is_mem_addr_addr >= 64'h00000000C0000000 &&
	     m_is_mem_addr_addr < 64'h0000000100000000 ;

  assign m_is_IO_addr =
	     NOT_m_is_IO_addr_addr_ULT_0xC000000_AND_m_is_I_ETC___d82 ||
	     !m_is_IO_addr_addr_ULT_0x30000000___d80 &&
	     m_is_IO_addr_addr_ULT_1073741824___d13 ;

  assign m_is_near_mem_IO_addr =
	     m_is_near_mem_IO_addr_addr >= 64'h0000000010000000 &&
	     m_is_near_mem_IO_addr_addr < 64'd268500992 ;

  assign m_pc_reset_value = 64'h0000000070000000 ;

  assign m_mtvec_reset_value = 64'h0000000000001000 ;

  assign m_nmivec_reset_value = 64'hAAAAAAAAAAAAAAAA ;

  assign NOT_m_is_IO_addr_addr_ULT_0xC000000_AND_m_is_I_ETC___d37 =
	     m_is_IO_addr_addr >= 64'h000000000C000000 &&
	     m_is_IO_addr_addr < 64'd205520896 ||
	     m_is_IO_addr_addr >= 64'h0000000010000000 &&
	     m_is_IO_addr_addr < 64'd268500992 ||
	     !m_is_IO_addr_addr_ULT_1073741824___d13 &&
	     m_is_IO_addr_addr < 64'd1207959552 ||
	     m_is_IO_addr_addr >= 64'h0000000062100000 &&
	     m_is_IO_addr_addr < 64'd1645477888 ||
	     m_is_IO_addr_addr >= 64'h0000000062200000 &&
	     m_is_IO_addr_addr < 64'd1646329856 ||
	     m_is_IO_addr_addr >= 64'h0000000062300000 &&
	     m_is_IO_addr_addr < 64'd1647316992 ||
	     m_is_IO_addr_addr >= 64'h000000006FFF0000 &&
	     m_is_IO_addr_addr_ULT_0x70000000___d35 ;
  assign NOT_m_is_IO_addr_addr_ULT_0xC000000_AND_m_is_I_ETC___d82 =
	     NOT_m_is_IO_addr_addr_ULT_0xC000000_AND_m_is_I_ETC___d37 ||
	     !m_is_IO_addr_addr_ULT_0x70000000___d35 &&
	     m_is_IO_addr_addr < 64'd1879052288 ||
	     m_is_IO_addr_addr >= 64'h0000000080000000 &&
	     m_is_IO_addr_addr < 64'h00000000C0000000 ||
	     m_is_IO_addr_addr >= 64'h0000000062400000 &&
	     m_is_IO_addr_addr < 64'd1648365568 ||
	     m_is_IO_addr_addr >= 64'h0000000062310000 &&
	     m_is_IO_addr_addr < 64'd1647382528 ||
	     m_is_IO_addr_addr >= 64'h0000000062320000 &&
	     m_is_IO_addr_addr < 64'd1647448064 ||
	     m_is_IO_addr_addr >= 64'h0000000062360000 &&
	     m_is_IO_addr_addr < 64'd1647710208 ||
	     m_is_IO_addr_addr >= 64'h0000000062330000 &&
	     m_is_IO_addr_addr < 64'd1647513600 ||
	     m_is_IO_addr_addr >= 64'h0000000062370000 &&
	     m_is_IO_addr_addr < 64'd1647775744 ||
	     m_is_IO_addr_addr >= 64'h0000000020000000 &&
	     m_is_IO_addr_addr_ULT_0x30000000___d80 ;
  assign m_is_IO_addr_addr_ULT_0x30000000___d80 =
	     m_is_IO_addr_addr < 64'h0000000030000000 ;
  assign m_is_IO_addr_addr_ULT_0x70000000___d35 =
	     m_is_IO_addr_addr < 64'h0000000070000000 ;
  assign m_is_IO_addr_addr_ULT_1073741824___d13 =
	     m_is_IO_addr_addr < 64'd1073741824 ;
endmodule  