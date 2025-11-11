// SVA for mkSoC_Map
// Concise, high-quality checks of address map coherence, function outputs, and coverage.

bind mkSoC_Map mkSoC_Map_sva u_mkSoC_Map_sva (.*);

module mkSoC_Map_sva (
  input  logic        CLK,
  input  logic        RST_N,

  input  logic [63:0] m_plic_addr_base,
  input  logic [63:0] m_plic_addr_size,
  input  logic [63:0] m_plic_addr_lim,

  input  logic [63:0] m_near_mem_io_addr_base,
  input  logic [63:0] m_near_mem_io_addr_size,
  input  logic [63:0] m_near_mem_io_addr_lim,

  input  logic [63:0] m_flash_mem_addr_base,
  input  logic [63:0] m_flash_mem_addr_size,
  input  logic [63:0] m_flash_mem_addr_lim,

  input  logic [63:0] m_ethernet_0_addr_base,
  input  logic [63:0] m_ethernet_0_addr_size,
  input  logic [63:0] m_ethernet_0_addr_lim,

  input  logic [63:0] m_dma_0_addr_base,
  input  logic [63:0] m_dma_0_addr_size,
  input  logic [63:0] m_dma_0_addr_lim,

  input  logic [63:0] m_uart16550_0_addr_base,
  input  logic [63:0] m_uart16550_0_addr_size,
  input  logic [63:0] m_uart16550_0_addr_lim,

  input  logic [63:0] m_gpio_0_addr_base,
  input  logic [63:0] m_gpio_0_addr_size,
  input  logic [63:0] m_gpio_0_addr_lim,

  input  logic [63:0] m_boot_rom_addr_base,
  input  logic [63:0] m_boot_rom_addr_size,
  input  logic [63:0] m_boot_rom_addr_lim,

  input  logic [63:0] m_ddr4_0_uncached_addr_base,
  input  logic [63:0] m_ddr4_0_uncached_addr_size,
  input  logic [63:0] m_ddr4_0_uncached_addr_lim,

  input  logic [63:0] m_ddr4_0_cached_addr_base,
  input  logic [63:0] m_ddr4_0_cached_addr_size,
  input  logic [63:0] m_ddr4_0_cached_addr_lim,

  input  logic [63:0] m_is_mem_addr_addr,
  input  logic        m_is_mem_addr,

  input  logic [63:0] m_is_IO_addr_addr,
  input  logic        m_is_IO_addr,

  input  logic [63:0] m_is_near_mem_IO_addr_addr,
  input  logic        m_is_near_mem_IO_addr,

  input  logic [63:0] m_pc_reset_value,
  input  logic [63:0] m_mtvec_reset_value,
  input  logic [63:0] m_nmivec_reset_value
);

  default clocking cb @(posedge CLK); endclocking
  default disable iff (!RST_N);

  function automatic bit in_range (logic [63:0] a, logic [63:0] base, logic [63:0] lim);
    return (a >= base) && (a < lim);
  endfunction

  function automatic bit is_pow2 (logic [63:0] v);
    return (v != 64'd0) && ((v & (v - 64'd1)) == 64'd0);
  endfunction

  // Constant/coherency checks (power-of-two size, alignment, limit = base + size)
  initial begin
    // PLIC
    assert (is_pow2(m_plic_addr_size)) else $error("PLIC size not power-of-two");
    assert (m_plic_addr_lim == m_plic_addr_base + m_plic_addr_size) else $error("PLIC lim!=base+size");
    assert ((m_plic_addr_base & (m_plic_addr_size-1)) == 0) else $error("PLIC base misaligned");
    // Near-IO
    assert (is_pow2(m_near_mem_io_addr_size)) else $error("NEAR-IO size not power-of-two");
    assert (m_near_mem_io_addr_lim == m_near_mem_io_addr_base + m_near_mem_io_addr_size) else $error("NEAR-IO lim");
    assert ((m_near_mem_io_addr_base & (m_near_mem_io_addr_size-1)) == 0) else $error("NEAR-IO base misaligned");
    // Flash
    assert (is_pow2(m_flash_mem_addr_size)) else $error("FLASH size not power-of-two");
    assert (m_flash_mem_addr_lim == m_flash_mem_addr_base + m_flash_mem_addr_size) else $error("FLASH lim");
    assert ((m_flash_mem_addr_base & (m_flash_mem_addr_size-1)) == 0) else $error("FLASH base misaligned");
    // Ethernet
    assert (is_pow2(m_ethernet_0_addr_size)) else $error("ETH size not power-of-two");
    assert (m_ethernet_0_addr_lim == m_ethernet_0_addr_base + m_ethernet_0_addr_size) else $error("ETH lim");
    assert ((m_ethernet_0_addr_base & (m_ethernet_0_addr_size-1)) == 0) else $error("ETH base misaligned");
    // DMA
    assert (is_pow2(m_dma_0_addr_size)) else $error("DMA size not power-of-two");
    assert (m_dma_0_addr_lim == m_dma_0_addr_base + m_dma_0_addr_size) else $error("DMA lim");
    assert ((m_dma_0_addr_base & (m_dma_0_addr_size-1)) == 0) else $error("DMA base misaligned");
    // UART
    assert (is_pow2(m_uart16550_0_addr_size)) else $error("UART size not power-of-two");
    assert (m_uart16550_0_addr_lim == m_uart16550_0_addr_base + m_uart16550_0_addr_size) else $error("UART lim");
    assert ((m_uart16550_0_addr_base & (m_uart16550_0_addr_size-1)) == 0) else $error("UART base misaligned");
    // GPIO
    assert (is_pow2(m_gpio_0_addr_size)) else $error("GPIO size not power-of-two");
    assert (m_gpio_0_addr_lim == m_gpio_0_addr_base + m_gpio_0_addr_size) else $error("GPIO lim");
    assert ((m_gpio_0_addr_base & (m_gpio_0_addr_size-1)) == 0) else $error("GPIO base misaligned");
    // Boot ROM
    assert (is_pow2(m_boot_rom_addr_size)) else $error("BOOTROM size not power-of-two");
    assert (m_boot_rom_addr_lim == m_boot_rom_addr_base + m_boot_rom_addr_size) else $error("BOOTROM lim");
    assert ((m_boot_rom_addr_base & (m_boot_rom_addr_size-1)) == 0) else $error("BOOTROM base misaligned");
    // DDR4 uncached
    assert (is_pow2(m_ddr4_0_uncached_addr_size)) else $error("DDR4-UNC size not power-of-two");
    assert (m_ddr4_0_uncached_addr_lim == m_ddr4_0_uncached_addr_base + m_ddr4_0_uncached_addr_size) else $error("DDR4-UNC lim");
    assert ((m_ddr4_0_uncached_addr_base & (m_ddr4_0_uncached_addr_size-1)) == 0) else $error("DDR4-UNC base misaligned");
    // DDR4 cached
    assert (is_pow2(m_ddr4_0_cached_addr_size)) else $error("DDR4-C size not power-of-two");
    assert (m_ddr4_0_cached_addr_lim == m_ddr4_0_cached_addr_base + m_ddr4_0_cached_addr_size) else $error("DDR4-C lim");
    assert ((m_ddr4_0_cached_addr_base & (m_ddr4_0_cached_addr_size-1)) == 0) else $error("DDR4-C base misaligned");

    // Address space ordering / non-overlap (monotonic by base)
    assert (m_plic_addr_lim                  <= m_near_mem_io_addr_base) else $error("PLIC overlaps NEAR-IO");
    assert (m_near_mem_io_addr_lim           <= m_flash_mem_addr_base)   else $error("NEAR-IO overlaps FLASH");
    assert (m_flash_mem_addr_lim             <= m_ethernet_0_addr_base)  else $error("FLASH overlaps ETH");
    assert (m_ethernet_0_addr_lim            <= m_dma_0_addr_base)       else $error("ETH overlaps DMA");
    assert (m_dma_0_addr_lim                 <= m_uart16550_0_addr_base) else $error("DMA overlaps UART");
    assert (m_uart16550_0_addr_lim           <= m_gpio_0_addr_base)      else $error("UART overlaps GPIO");
    assert (m_gpio_0_addr_lim                <= m_boot_rom_addr_base)    else $error("GPIO overlaps BOOTROM");
    assert (m_boot_rom_addr_lim              <= m_ddr4_0_uncached_addr_base) else $error("BOOTROM overlaps DDR4-UNC");
    assert (m_ddr4_0_uncached_addr_lim == m_ddr4_0_cached_addr_base) else $error("DDR4-UNC/C not abutting");
    assert (m_ddr4_0_uncached_addr_size == m_ddr4_0_cached_addr_size) else $error("DDR4 sizes mismatch");

    // Reset vector sanity
    assert (m_pc_reset_value == m_boot_rom_addr_base) else $error("PC reset not at BOOTROM base");
    assert (m_mtvec_reset_value[1:0] == 2'b00) else $error("mtvec not 4-byte aligned");
  end

  // Outputs stable after reset deassertion
  property p_stable_const_outputs;
    $stable({
      m_plic_addr_base, m_plic_addr_size, m_plic_addr_lim,
      m_near_mem_io_addr_base, m_near_mem_io_addr_size, m_near_mem_io_addr_lim,
      m_flash_mem_addr_base, m_flash_mem_addr_size, m_flash_mem_addr_lim,
      m_ethernet_0_addr_base, m_ethernet_0_addr_size, m_ethernet_0_addr_lim,
      m_dma_0_addr_base, m_dma_0_addr_size, m_dma_0_addr_lim,
      m_uart16550_0_addr_base, m_uart16550_0_addr_size, m_uart16550_0_addr_lim,
      m_gpio_0_addr_base, m_gpio_0_addr_size, m_gpio_0_addr_lim,
      m_boot_rom_addr_base, m_boot_rom_addr_size, m_boot_rom_addr_lim,
      m_ddr4_0_uncached_addr_base, m_ddr4_0_uncached_addr_size, m_ddr4_0_uncached_addr_lim,
      m_ddr4_0_cached_addr_base, m_ddr4_0_cached_addr_size, m_ddr4_0_cached_addr_lim,
      m_pc_reset_value, m_mtvec_reset_value, m_nmivec_reset_value
    });
  endproperty
  assert property (p_stable_const_outputs);

  // Functional correctness: exact predicates for the boolean outputs
  assert property (m_is_mem_addr == in_range(m_is_mem_addr_addr, m_ddr4_0_cached_addr_base, m_ddr4_0_cached_addr_lim));
  assert property (m_is_near_mem_IO_addr == in_range(m_is_near_mem_IO_addr_addr, m_near_mem_io_addr_base, m_near_mem_io_addr_lim));

  // IO must assert when address falls in any of the main published IO windows
  property p_io_must_cover_published_windows;
    in_range(m_is_IO_addr_addr, m_plic_addr_base,              m_plic_addr_lim)              ||
    in_range(m_is_IO_addr_addr, m_near_mem_io_addr_base,       m_near_mem_io_addr_lim)       ||
    in_range(m_is_IO_addr_addr, m_flash_mem_addr_base,         m_flash_mem_addr_lim)         ||
    in_range(m_is_IO_addr_addr, m_ethernet_0_addr_base,        m_ethernet_0_addr_lim)        ||
    in_range(m_is_IO_addr_addr, m_dma_0_addr_base,             m_dma_0_addr_lim)             ||
    in_range(m_is_IO_addr_addr, m_uart16550_0_addr_base,       m_uart16550_0_addr_lim)       ||
    in_range(m_is_IO_addr_addr, m_gpio_0_addr_base,            m_gpio_0_addr_lim)            ||
    in_range(m_is_IO_addr_addr, m_boot_rom_addr_base,          m_boot_rom_addr_lim)          ||
    in_range(m_is_IO_addr_addr, m_ddr4_0_uncached_addr_base,   m_ddr4_0_uncached_addr_lim)
    |-> m_is_IO_addr;
  endproperty
  assert property (p_io_must_cover_published_windows);

  // IO must be deasserted in well-known gaps (negative spaces)
  assert property (in_range(m_is_IO_addr_addr, 64'h0000_0000,              m_plic_addr_base)            |-> !m_is_IO_addr);
  assert property (in_range(m_is_IO_addr_addr, m_plic_addr_lim,            m_near_mem_io_addr_base)     |-> !m_is_IO_addr);
  assert property (in_range(m_is_IO_addr_addr, m_near_mem_io_addr_lim,     64'h2000_0000)               |-> !m_is_IO_addr);
  assert property (in_range(m_is_IO_addr_addr, 64'h3000_0000,              64'h4000_0000)               |-> !m_is_IO_addr);
  assert property (in_range(m_is_IO_addr_addr, m_flash_mem_addr_lim,       m_ethernet_0_addr_base)      |-> !m_is_IO_addr);
  assert property (in_range(m_is_IO_addr_addr, m_uart16550_0_addr_lim,     m_gpio_0_addr_base)          |-> !m_is_IO_addr);
  assert property (in_range(m_is_IO_addr_addr, m_gpio_0_addr_lim,          m_boot_rom_addr_base)        |-> !m_is_IO_addr);
  assert property (in_range(m_is_IO_addr_addr, m_boot_rom_addr_lim,        m_ddr4_0_uncached_addr_base) |-> !m_is_IO_addr);
  assert property (in_range(m_is_IO_addr_addr, m_ddr4_0_cached_addr_base,  m_ddr4_0_cached_addr_lim)    |-> !m_is_IO_addr);
  assert property (m_is_IO_addr_addr >= m_ddr4_0_cached_addr_lim |-> !m_is_IO_addr);

  // Output knownness (no X/Z)
  assert property (!$isunknown({
    m_is_mem_addr, m_is_IO_addr, m_is_near_mem_IO_addr,
    m_plic_addr_base, m_plic_addr_size, m_plic_addr_lim,
    m_near_mem_io_addr_base, m_near_mem_io_addr_size, m_near_mem_io_addr_lim,
    m_flash_mem_addr_base, m_flash_mem_addr_size, m_flash_mem_addr_lim,
    m_ethernet_0_addr_base, m_ethernet_0_addr_size, m_ethernet_0_addr_lim,
    m_dma_0_addr_base, m_dma_0_addr_size, m_dma_0_addr_lim,
    m_uart16550_0_addr_base, m_uart16550_0_addr_size, m_uart16550_0_addr_lim,
    m_gpio_0_addr_base, m_gpio_0_addr_size, m_gpio_0_addr_lim,
    m_boot_rom_addr_base, m_boot_rom_addr_size, m_boot_rom_addr_lim,
    m_ddr4_0_uncached_addr_base, m_ddr4_0_uncached_addr_size, m_ddr4_0_uncached_addr_lim,
    m_ddr4_0_cached_addr_base, m_ddr4_0_cached_addr_size, m_ddr4_0_cached_addr_lim,
    m_pc_reset_value, m_mtvec_reset_value, m_nmivec_reset_value
  }));

  // Coverage: hit each published region with correct classification
  cover property (in_range(m_is_IO_addr_addr, m_plic_addr_base,            m_plic_addr_lim)            && m_is_IO_addr);
  cover property (in_range(m_is_IO_addr_addr, m_near_mem_io_addr_base,     m_near_mem_io_addr_lim)     && m_is_IO_addr);
  cover property (in_range(m_is_IO_addr_addr, m_flash_mem_addr_base,       m_flash_mem_addr_lim)       && m_is_IO_addr);
  cover property (in_range(m_is_IO_addr_addr, m_ethernet_0_addr_base,      m_ethernet_0_addr_lim)      && m_is_IO_addr);
  cover property (in_range(m_is_IO_addr_addr, m_dma_0_addr_base,           m_dma_0_addr_lim)           && m_is_IO_addr);
  cover property (in_range(m_is_IO_addr_addr, m_uart16550_0_addr_base,     m_uart16550_0_addr_lim)     && m_is_IO_addr);
  cover property (in_range(m_is_IO_addr_addr, m_gpio_0_addr_base,          m_gpio_0_addr_lim)          && m_is_IO_addr);
  cover property (in_range(m_is_IO_addr_addr, m_boot_rom_addr_base,        m_boot_rom_addr_lim)        && m_is_IO_addr);
  cover property (in_range(m_is_IO_addr_addr, m_ddr4_0_uncached_addr_base, m_ddr4_0_uncached_addr_lim) && m_is_IO_addr);
  cover property (in_range(m_is_mem_addr_addr, m_ddr4_0_cached_addr_base,  m_ddr4_0_cached_addr_lim)   && m_is_mem_addr);
  cover property (in_range(m_is_near_mem_IO_addr_addr, m_near_mem_io_addr_base, m_near_mem_io_addr_lim) && m_is_near_mem_IO_addr);

  // Boundary coverage
  cover property ((m_is_IO_addr_addr == m_plic_addr_base)                     && m_is_IO_addr);
  cover property ((m_is_IO_addr_addr == m_plic_addr_lim-1)                    && m_is_IO_addr);
  cover property ((m_is_mem_addr_addr == m_ddr4_0_cached_addr_base)           && m_is_mem_addr);
  cover property ((m_is_mem_addr_addr == m_ddr4_0_cached_addr_lim-1)          && m_is_mem_addr);
  cover property ((m_is_IO_addr_addr == m_ddr4_0_uncached_addr_base)          && m_is_IO_addr);
  cover property ((m_is_IO_addr_addr == m_ddr4_0_uncached_addr_lim-1)         && m_is_IO_addr);

endmodule