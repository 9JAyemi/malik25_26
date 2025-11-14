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

		 m_near_mem_io_addr_base,

		 m_near_mem_io_addr_size,

		 m_near_mem_io_addr_lim,

		 m_plic_addr_base,

		 m_plic_addr_size,

		 m_plic_addr_lim,

		 m_uart0_addr_base,

		 m_uart0_addr_size,

		 m_uart0_addr_lim,

		 m_boot_rom_addr_base,

		 m_boot_rom_addr_size,

		 m_boot_rom_addr_lim,

		 m_mem0_controller_addr_base,

		 m_mem0_controller_addr_size,

		 m_mem0_controller_addr_lim,

		 m_tcm_addr_base,

		 m_tcm_addr_size,

		 m_tcm_addr_lim,

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

  output [63 : 0] m_near_mem_io_addr_base;

  output [63 : 0] m_near_mem_io_addr_size;

  output [63 : 0] m_near_mem_io_addr_lim;

  output [63 : 0] m_plic_addr_base;

  output [63 : 0] m_plic_addr_size;

  output [63 : 0] m_plic_addr_lim;

  output [63 : 0] m_uart0_addr_base;

  output [63 : 0] m_uart0_addr_size;

  output [63 : 0] m_uart0_addr_lim;

  output [63 : 0] m_boot_rom_addr_base;

  output [63 : 0] m_boot_rom_addr_size;

  output [63 : 0] m_boot_rom_addr_lim;

  output [63 : 0] m_mem0_controller_addr_base;

  output [63 : 0] m_mem0_controller_addr_size;

  output [63 : 0] m_mem0_controller_addr_lim;

  output [63 : 0] m_tcm_addr_base;

  output [63 : 0] m_tcm_addr_size;

  output [63 : 0] m_tcm_addr_lim;

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
		m_mem0_controller_addr_base,
		m_mem0_controller_addr_lim,
		m_mem0_controller_addr_size,
		m_mtvec_reset_value,
		m_near_mem_io_addr_base,
		m_near_mem_io_addr_lim,
		m_near_mem_io_addr_size,
		m_nmivec_reset_value,
		m_pc_reset_value,
		m_plic_addr_base,
		m_plic_addr_lim,
		m_plic_addr_size,
		m_tcm_addr_base,
		m_tcm_addr_lim,
		m_tcm_addr_size,
		m_uart0_addr_base,
		m_uart0_addr_lim,
		m_uart0_addr_size;
  wire m_is_IO_addr, m_is_mem_addr, m_is_near_mem_IO_addr;

  assign m_near_mem_io_addr_base = 64'h0000000002000000 ;

  assign m_near_mem_io_addr_size = 64'h000000000000C000 ;

  assign m_near_mem_io_addr_lim = 64'd33603584 ;

  assign m_plic_addr_base = 64'h000000000C000000 ;

  assign m_plic_addr_size = 64'h0000000000400000 ;

  assign m_plic_addr_lim = 64'd205520896 ;

  assign m_uart0_addr_base = 64'h00000000C0000000 ;

  assign m_uart0_addr_size = 64'h0000000000000080 ;

  assign m_uart0_addr_lim = 64'h00000000C0000080 ;

  assign m_boot_rom_addr_base = 64'h0000000000001000 ;

  assign m_boot_rom_addr_size = 64'h0000000000001000 ;

  assign m_boot_rom_addr_lim = 64'd8192 ;

  assign m_mem0_controller_addr_base = 64'h0000000080000000 ;

  assign m_mem0_controller_addr_size = 64'h0000000010000000 ;

  assign m_mem0_controller_addr_lim = 64'h0000000090000000 ;

  assign m_tcm_addr_base = 64'h0 ;

  assign m_tcm_addr_size = 64'd0 ;

  assign m_tcm_addr_lim = 64'd0 ;

  assign m_is_mem_addr =
	     m_is_mem_addr_addr >= 64'h0000000000001000 &&
	     m_is_mem_addr_addr < 64'd8192 ||
	     m_is_mem_addr_addr >= 64'h0000000080000000 &&
	     m_is_mem_addr_addr < 64'h0000000090000000 ;

  assign m_is_IO_addr =
	     m_is_IO_addr_addr >= 64'h0000000002000000 &&
	     m_is_IO_addr_addr < 64'd33603584 ||
	     m_is_IO_addr_addr >= 64'h000000000C000000 &&
	     m_is_IO_addr_addr < 64'd205520896 ||
	     m_is_IO_addr_addr >= 64'h00000000C0000000 &&
	     m_is_IO_addr_addr < 64'h00000000C0000080 ;

  assign m_is_near_mem_IO_addr =
	     m_is_near_mem_IO_addr_addr >= 64'h0000000002000000 &&
	     m_is_near_mem_IO_addr_addr < 64'd33603584 ;

  assign m_pc_reset_value = 64'h0000000000001000 ;

  assign m_mtvec_reset_value = 64'h0000000000001000 ;

  assign m_nmivec_reset_value = 64'hAAAAAAAAAAAAAAAA ;
endmodule  