// SVA for bus_manager (bind-in, no DUT edits)

bind bus_manager bus_manager_sva bm_sva();

module bus_manager_sva;

  // Combinational equivalence and priority checks
  always @* begin
    // Basic decodes
    assert (ROM_cs === addr[15]) else $error("ROM_cs decode wrong");

    if (game_sel) begin
      assert (RAM_cs     === (cpu_vma && (addr >= 16'h0000 && addr <= 16'h0FFF))) else $error("DDRAGON RAM_cs");
      assert (opm_cs_n   === !(cpu_vma && (addr >= 16'h2800 && addr <= 16'h2801))) else $error("DDRAGON opm_cs_n");
      assert (LATCH_rd   === (cpu_vma && addr == 16'h1000))                      else $error("DDRAGON LATCH_rd");
      assert (irq_clear_addr === 16'h1000)                                       else $error("DDRAGON irq_clear_addr");
    end else begin
      assert (RAM_cs     === (cpu_vma && (addr >= 16'h6000 && addr <= 16'h7FFF))) else $error("CONTRA RAM_cs");
      assert (opm_cs_n   === !(cpu_vma && (!addr[15] && !addr[14] && addr[13])))  else $error("CONTRA opm_cs_n");
      assert (LATCH_rd   === (cpu_vma && addr == 16'h0000))                       else $error("CONTRA LATCH_rd");
      assert (irq_clear_addr === 16'h4000)                                        else $error("CONTRA irq_clear_addr");
    end

    assert (clear_irq === (cpu_vma && (addr == irq_clear_addr))) else $error("clear_irq decode");

    // Selects should not overlap (given address map)
    if (cpu_vma) begin
      assert (!(~opm_cs_n && RAM_cs))   else $error("Overlap: OPM & RAM");
      assert (!(~opm_cs_n && ROM_cs))   else $error("Overlap: OPM & ROM");
      assert (!(~opm_cs_n && LATCH_rd)) else $error("Overlap: OPM & LATCH");
      assert (!(RAM_cs && ROM_cs))      else $error("Overlap: RAM & ROM");
      assert (!(RAM_cs && LATCH_rd))    else $error("Overlap: RAM & LATCH");
      assert (!(ROM_cs && LATCH_rd))    else $error("Overlap: ROM & LATCH");
    end

    // Data mux priority (guard unknown controls)
    if (!$isunknown({cpu_rw,cpu_vma,opm_cs_n,RAM_cs,ROM_cs,LATCH_rd})) begin
      if (cpu_rw && cpu_vma) begin
        if      (~opm_cs_n) assert (cpu_data_in === jt_data_out)  else $error("mux->OPM");
        else if (RAM_cs)    assert (cpu_data_in === RAM_data)     else $error("mux->RAM");
        else if (ROM_cs)    assert (cpu_data_in === ROM_data_out) else $error("mux->ROM");
        else if (LATCH_rd)  assert (cpu_data_in === sound_latch)  else $error("mux->LATCH");
        else                assert (cpu_data_in === 8'h00)        else $error("mux->default");
      end else begin
        assert (cpu_data_in === 8'h00) else $error("mux gating when !read or !vma");
      end
    end

    // No X on output when a valid read source is selected
    if (cpu_rw && cpu_vma && (~opm_cs_n | RAM_cs | ROM_cs | LATCH_rd))
      assert (!$isunknown(cpu_data_in)) else $error("cpu_data_in is X on read");
  end

  // Functional coverage (immediate covers)
  // Exercise each data source
  cover (cpu_rw && cpu_vma && ~opm_cs_n);
  cover (cpu_rw && cpu_vma && RAM_cs);
  cover (cpu_rw && cpu_vma && ROM_cs);
  cover (cpu_rw && cpu_vma && LATCH_rd);

  // Game-specific decodes
  cover (game_sel  && cpu_vma && (addr >= 16'h0000 && addr <= 16'h0FFF) && RAM_cs);
  cover (!game_sel && cpu_vma && (addr >= 16'h6000 && addr <= 16'h7FFF) && RAM_cs);
  cover (game_sel  && cpu_vma && addr == 16'h1000 && LATCH_rd && clear_irq);
  cover (!game_sel && cpu_vma && addr == 16'h4000 && clear_irq);
  cover (game_sel  && cpu_vma && (addr >= 16'h2800 && addr <= 16'h2801) && ~opm_cs_n);
  cover (!game_sel && cpu_vma && (!addr[15] && !addr[14] && addr[13]) && ~opm_cs_n);

endmodule