// SVA for BIOS_ROM_blk_mem_gen_prim_width
// Concise checker with a cycle-accurate reference model (READ_FIRST behavior)

module BIOS_ROM_blk_mem_gen_prim_width_sva;

  default clocking cb @(posedge clka); endclocking

  // Reference model of the memory and expected output
  logic [7:0] ref_mem [0:4095];
  logic [7:0] exp_dout;
  bit vld;

  // Model updates (mirrors DUT semantics: read-first, enable-gated)
  always_ff @(posedge clka) begin
    if (ena) begin
      exp_dout <= ref_mem[addra];
      if (wea) ref_mem[addra] <= dina;
      vld <= 1'b1;
    end
  end

  // Inputs must be known when used
  a_no_x_inputs_when_ena: assert property (ena |-> !$isunknown({addra, dina, wea}));

  // Output must hold when disabled
  a_hold_when_disabled:   assert property (!ena |-> $stable(douta));

  // Equivalence to the reference model (use case equality to tolerate X before first enable)
  a_dout_matches_model:   assert property (vld |-> (douta === exp_dout));

  // Write then next-cycle read of same address returns written data
  a_raw_same_addr: assert property (
    $past(ena && wea) && ena && (addra == $past(addra)) |-> (douta === $past(dina))
  );

  // Coverage
  c_write: cover property (ena && wea);
  c_read:  cover property (ena && !wea);
  c_raw:   cover property ((ena && wea) ##1 (ena && !wea && (addra == $past(addra))));
  c_b2b:   cover property ((ena && !wea) ##1 (ena && !wea && (addra != $past(addra))));

endmodule

bind BIOS_ROM_blk_mem_gen_prim_width BIOS_ROM_blk_mem_gen_prim_width_sva sva_inst();