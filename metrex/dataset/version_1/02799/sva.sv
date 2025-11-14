// SVA checker for blk_mem_gen_0blk_mem_gen_top
// Focused, high-signal-coverage, concise

// Bind this checker to the DUT
bind blk_mem_gen_0blk_mem_gen_top blk_mem_gen_0blk_mem_gen_top_sva sva_i(
  .clka(clka), .clkb(clkb), .enb(enb), .wea(wea), .addra(addra), .addrb(addrb),
  .dina(dina), .doutb(doutb)
);

module blk_mem_gen_0blk_mem_gen_top_sva
(
  input  logic        clka,
  input  logic        clkb,
  input  logic        enb,
  input  logic [0:0]  wea,
  input  logic [8:0]  addra,
  input  logic [8:0]  addrb,
  input  logic [63:0] dina,
  input  logic [63:0] doutb
);

  // Lightweight shadow model for functional checking
  logic [63:0] mem_mirror [0:511];

  // Update model only on clean, valid writes
  always_ff @(posedge clka) begin
    if (enb && (wea[0] === 1'b1) && !$isunknown({addra,dina}))
      mem_mirror[addra] <= dina;
  end

  // 1) Basic input sanity (no X on controls/addresses when used)
  a_no_x_ctrl_clka: assert property (@(posedge clka) !$isunknown({enb,wea,addra}));
  a_no_x_addrb_clkb: assert property (@(posedge clkb) !$isunknown(addrb));

  // 2) Read data must equal model at all observed times (when known)
  property p_dout_matches(clk);
    @(posedge clk)
      (!$isunknown(addrb) && !$isunknown(mem_mirror[addrb])) |-> (doutb == mem_mirror[addrb]);
  endproperty
  a_dout_match_clka: assert property (p_dout_matches(clka));
  a_dout_match_clkb: assert property (p_dout_matches(clkb));

  // 3) Write-hit-on-read behavior (observed 1 cycle later on clka)
  //    If writing A on clka and read address is A, next clka sample must reflect new data
  a_raw_same_addr_update: assert property (
    @(posedge clka)
      (enb && wea[0] && !$isunknown({addra,dina}) && (addra == addrb))
      |=> (doutb == $past(dina))
  );

  // 4) Disabled write (wea=1, enb=0) must NOT affect the read value of that address
  a_disabled_write_no_effect: assert property (
    @(posedge clka)
      (wea[0] && !enb && !$isunknown(addra) && (addra == addrb))
      |=> (doutb == $past(mem_mirror[addrb]))
  );

  // 5) If read address is stable and no write to that address, doutb must be stable
  property p_stable_read_if_no_write(clk);
    @(posedge clk)
      $stable(addrb) && !(enb && wea[0] && (addra == addrb)) |-> $stable(doutb);
  endproperty
  a_stable_read_clka: assert property (p_stable_read_if_no_write(clka));
  a_stable_read_clkb: assert property (p_stable_read_if_no_write(clkb));

  // 6) Controls are strictly 0/1 (no X/Z) when sampled on clka
  a_ctrl_01_only: assert property (@(posedge clka) (wea[0] === 1'b0) || (wea[0] === 1'b1));
  a_enb_01_only:  assert property (@(posedge clka) (enb    === 1'b0) || (enb    === 1'b1));

  // -----------------------------------
  // Coverage (exercise key behaviors)
  // -----------------------------------
  // At least one valid write
  c_write:          cover property (@(posedge clka) enb && wea[0] && !$isunknown({addra,dina}));

  // Boundary writes
  c_write_low:      cover property (@(posedge clka) enb && wea[0] && (addra == 9'h000));
  c_write_high:     cover property (@(posedge clka) enb && wea[0] && (addra == 9'h1FF));

  // Back-to-back writes (same address and different address)
  c_b2b_same:       cover property (@(posedge clka)
                          enb && wea[0] ##1 enb && wea[0] && ($past(addra) == addra));
  c_b2b_diff:       cover property (@(posedge clka)
                          enb && wea[0] ##1 enb && wea[0] && ($past(addra) != addra));

  // Write-then-read same address
  c_wr_then_rd:     cover property (@(posedge clka)
                          enb && wea[0] ##[1:10] (addrb == $past(addra)));

  // Disabled write attempt observed on same address
  c_disabled_wr:    cover property (@(posedge clka) wea[0] && !enb && (addra == addrb));

  // Activity on read clock (though not used by DUT logic)
  c_clkb_tog:       cover property (@(posedge clkb) 1);

endmodule