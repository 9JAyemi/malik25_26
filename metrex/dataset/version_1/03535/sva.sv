// SVA for mkSoC_Map
// Bind this file to the DUT: bind mkSoC_Map mkSoC_Map_sva sva_i (.*);

`ifndef BSV_RESET_VALUE
  `define BSV_RESET_VALUE 1'b0
`endif

module mkSoC_Map_sva (
  input logic CLK,
  input logic RST_N,

  input logic [63:0] m_near_mem_io_addr_base,
  input logic [63:0] m_near_mem_io_addr_size,
  input logic [63:0] m_near_mem_io_addr_lim,

  input logic [63:0] m_plic_addr_base,
  input logic [63:0] m_plic_addr_size,
  input logic [63:0] m_plic_addr_lim,

  input logic [63:0] m_uart0_addr_base,
  input logic [63:0] m_uart0_addr_size,
  input logic [63:0] m_uart0_addr_lim,

  input logic [63:0] m_boot_rom_addr_base,
  input logic [63:0] m_boot_rom_addr_size,
  input logic [63:0] m_boot_rom_addr_lim,

  input logic [63:0] m_mem0_controller_addr_base,
  input logic [63:0] m_mem0_controller_addr_size,
  input logic [63:0] m_mem0_controller_addr_lim,

  input logic [63:0] m_tcm_addr_base,
  input logic [63:0] m_tcm_addr_size,
  input logic [63:0] m_tcm_addr_lim,

  input logic [63:0] m_is_mem_addr_addr,
  input logic        m_is_mem_addr,

  input logic [63:0] m_is_IO_addr_addr,
  input logic        m_is_IO_addr,

  input logic [63:0] m_is_near_mem_IO_addr_addr,
  input logic        m_is_near_mem_IO_addr,

  input logic [63:0] m_pc_reset_value,
  input logic [63:0] m_mtvec_reset_value,
  input logic [63:0] m_nmivec_reset_value
);

  function automatic bit in_rng (logic [63:0] a, b, l);
    return (a >= b) && (a < l);
  endfunction

  // Constant value checks (one-time)
  initial begin
    // Exact constant encodings
    assert (m_near_mem_io_addr_base == 64'h0000_0000_0200_0000);
    assert (m_near_mem_io_addr_size == 64'h0000_0000_0000_C000);
    assert (m_near_mem_io_addr_lim  == 64'd33603584);

    assert (m_plic_addr_base == 64'h0000_0000_0C00_0000);
    assert (m_plic_addr_size == 64'h0000_0000_0040_0000);
    assert (m_plic_addr_lim  == 64'd205520896);

    assert (m_uart0_addr_base == 64'h0000_0000_C000_0000);
    assert (m_uart0_addr_size == 64'h0000_0000_0000_0080);
    assert (m_uart0_addr_lim  == 64'h0000_0000_C000_0080);

    assert (m_boot_rom_addr_base == 64'h0000_0000_0000_1000);
    assert (m_boot_rom_addr_size == 64'h0000_0000_0000_1000);
    assert (m_boot_rom_addr_lim  == 64'd8192);

    assert (m_mem0_controller_addr_base == 64'h0000_0000_8000_0000);
    assert (m_mem0_controller_addr_size == 64'h0000_0000_1000_0000);
    assert (m_mem0_controller_addr_lim  == 64'h0000_0000_9000_0000);

    assert (m_tcm_addr_base == 64'h0);
    assert (m_tcm_addr_size == 64'h0);
    assert (m_tcm_addr_lim  == 64'h0);

    assert (m_pc_reset_value    == 64'h0000_0000_0000_1000);
    assert (m_mtvec_reset_value == 64'h0000_0000_0000_1000);
    assert (m_nmivec_reset_value== 64'hAAAA_AAAA_AAAA_AAAA);

    // size/limit consistency
    assert (m_near_mem_io_addr_lim - m_near_mem_io_addr_base == m_near_mem_io_addr_size);
    assert (m_plic_addr_lim        - m_plic_addr_base        == m_plic_addr_size);
    assert (m_uart0_addr_lim       - m_uart0_addr_base       == m_uart0_addr_size);
    assert (m_boot_rom_addr_lim    - m_boot_rom_addr_base    == m_boot_rom_addr_size);
    assert (m_mem0_controller_addr_lim - m_mem0_controller_addr_base == m_mem0_controller_addr_size);
    assert (m_tcm_addr_lim         - m_tcm_addr_base         == m_tcm_addr_size);

    // Non-overlap (ordered map)
    assert (m_boot_rom_addr_lim          <= m_near_mem_io_addr_base);
    assert (m_near_mem_io_addr_lim       <= m_plic_addr_base);
    assert (m_plic_addr_lim              <= m_mem0_controller_addr_base);
    assert (m_mem0_controller_addr_lim   <= m_uart0_addr_base);
  end

  // Output signals are stable and known (never X/Z)
  assert property (@(posedge CLK) disable iff (RST_N == `BSV_RESET_VALUE)
                   $stable({ m_near_mem_io_addr_base, m_near_mem_io_addr_size, m_near_mem_io_addr_lim,
                             m_plic_addr_base, m_plic_addr_size, m_plic_addr_lim,
                             m_uart0_addr_base, m_uart0_addr_size, m_uart0_addr_lim,
                             m_boot_rom_addr_base, m_boot_rom_addr_size, m_boot_rom_addr_lim,
                             m_mem0_controller_addr_base, m_mem0_controller_addr_size, m_mem0_controller_addr_lim,
                             m_tcm_addr_base, m_tcm_addr_size, m_tcm_addr_lim,
                             m_pc_reset_value, m_mtvec_reset_value, m_nmivec_reset_value }))
    else $error("mkSoC_Map constants changed unexpectedly");

  assert property (@(posedge CLK)
                   !$isunknown({ m_near_mem_io_addr_base, m_near_mem_io_addr_size, m_near_mem_io_addr_lim,
                                 m_plic_addr_base, m_plic_addr_size, m_plic_addr_lim,
                                 m_uart0_addr_base, m_uart0_addr_size, m_uart0_addr_lim,
                                 m_boot_rom_addr_base, m_boot_rom_addr_size, m_boot_rom_addr_lim,
                                 m_mem0_controller_addr_base, m_mem0_controller_addr_size, m_mem0_controller_addr_lim,
                                 m_tcm_addr_base, m_tcm_addr_size, m_tcm_addr_lim,
                                 m_pc_reset_value, m_mtvec_reset_value, m_nmivec_reset_value }));

  // Classifier functional correctness
  assert property (@(posedge CLK) disable iff (RST_N == `BSV_RESET_VALUE)
    m_is_mem_addr == ( in_rng(m_is_mem_addr_addr, m_boot_rom_addr_base, m_boot_rom_addr_lim)
                    || in_rng(m_is_mem_addr_addr, m_mem0_controller_addr_base, m_mem0_controller_addr_lim)));

  assert property (@(posedge CLK) disable iff (RST_N == `BSV_RESET_VALUE)
    m_is_IO_addr == ( in_rng(m_is_IO_addr_addr, m_near_mem_io_addr_base, m_near_mem_io_addr_lim)
                   || in_rng(m_is_IO_addr_addr, m_plic_addr_base, m_plic_addr_lim)
                   || in_rng(m_is_IO_addr_addr, m_uart0_addr_base, m_uart0_addr_lim)));

  assert property (@(posedge CLK) disable iff (RST_N == `BSV_RESET_VALUE)
    m_is_near_mem_IO_addr == in_rng(m_is_near_mem_IO_addr_addr, m_near_mem_io_addr_base, m_near_mem_io_addr_lim));

  // Classifier not-X when address is known
  assert property (@(posedge CLK) !$isunknown(m_is_mem_addr_addr) |-> !$isunknown(m_is_mem_addr));
  assert property (@(posedge CLK) !$isunknown(m_is_IO_addr_addr)  |-> !$isunknown(m_is_IO_addr));
  assert property (@(posedge CLK) !$isunknown(m_is_near_mem_IO_addr_addr) |-> !$isunknown(m_is_near_mem_IO_addr));

  // Coverage: hit both outcomes and boundaries for each region
  // m_is_mem_addr (boot_rom range)
  cover property (@(posedge CLK) m_is_mem_addr);
  cover property (@(posedge CLK) !m_is_mem_addr);
  cover property (@(posedge CLK) m_is_mem_addr_addr == m_boot_rom_addr_base  && m_is_mem_addr);
  cover property (@(posedge CLK) m_is_mem_addr_addr == m_boot_rom_addr_lim-1 && m_is_mem_addr);
  cover property (@(posedge CLK) m_is_mem_addr_addr == m_boot_rom_addr_lim   && !m_is_mem_addr);
  cover property (@(posedge CLK) m_is_mem_addr_addr == m_boot_rom_addr_base-1&& !m_is_mem_addr);
  // m_is_mem_addr (mem0_controller range)
  cover property (@(posedge CLK) m_is_mem_addr_addr == m_mem0_controller_addr_base  && m_is_mem_addr);
  cover property (@(posedge CLK) m_is_mem_addr_addr == m_mem0_controller_addr_lim-1 && m_is_mem_addr);
  cover property (@(posedge CLK) m_is_mem_addr_addr == m_mem0_controller_addr_lim   && !m_is_mem_addr);
  cover property (@(posedge CLK) m_is_mem_addr_addr == m_mem0_controller_addr_base-1&& !m_is_mem_addr);

  // m_is_IO_addr (near_mem_io)
  cover property (@(posedge CLK) m_is_IO_addr_addr == m_near_mem_io_addr_base  && m_is_IO_addr);
  cover property (@(posedge CLK) m_is_IO_addr_addr == m_near_mem_io_addr_lim-1 && m_is_IO_addr);
  cover property (@(posedge CLK) m_is_IO_addr_addr == m_near_mem_io_addr_lim   && !m_is_IO_addr);
  cover property (@(posedge CLK) m_is_IO_addr_addr == m_near_mem_io_addr_base-1&& !m_is_IO_addr);
  // m_is_IO_addr (plic)
  cover property (@(posedge CLK) m_is_IO_addr_addr == m_plic_addr_base  && m_is_IO_addr);
  cover property (@(posedge CLK) m_is_IO_addr_addr == m_plic_addr_lim-1 && m_is_IO_addr);
  cover property (@(posedge CLK) m_is_IO_addr_addr == m_plic_addr_lim   && !m_is_IO_addr);
  cover property (@(posedge CLK) m_is_IO_addr_addr == m_plic_addr_base-1&& !m_is_IO_addr);
  // m_is_IO_addr (uart0)
  cover property (@(posedge CLK) m_is_IO_addr_addr == m_uart0_addr_base  && m_is_IO_addr);
  cover property (@(posedge CLK) m_is_IO_addr_addr == m_uart0_addr_lim-1 && m_is_IO_addr);
  cover property (@(posedge CLK) m_is_IO_addr_addr == m_uart0_addr_lim   && !m_is_IO_addr);
  cover property (@(posedge CLK) m_is_IO_addr_addr == m_uart0_addr_base-1&& !m_is_IO_addr);

  // m_is_near_mem_IO_addr boundaries
  cover property (@(posedge CLK) m_is_near_mem_IO_addr_addr == m_near_mem_io_addr_base  && m_is_near_mem_IO_addr);
  cover property (@(posedge CLK) m_is_near_mem_IO_addr_addr == m_near_mem_io_addr_lim-1 && m_is_near_mem_IO_addr);
  cover property (@(posedge CLK) m_is_near_mem_IO_addr_addr == m_near_mem_io_addr_lim   && !m_is_near_mem_IO_addr);
  cover property (@(posedge CLK) m_is_near_mem_IO_addr_addr == m_near_mem_io_addr_base-1&& !m_is_near_mem_IO_addr);

endmodule

// Bind to DUT
bind mkSoC_Map mkSoC_Map_sva sva_i (.*);