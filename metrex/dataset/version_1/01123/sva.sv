// SVA for dat_i_arbiter
// Bind into the DUT; focuses on correctness, priority, and coverage.

module dat_i_arbiter_sva (
  input logic         clock_i,
  input logic [7:0]   D,
  input logic [7:0]   l_rom,
  input logic         l_rom_e,
  input logic [7:0]   u_rom,
  input logic         u_rom_e,
  input logic [7:0]   ram,
  input logic         ram_e,
  input logic [7:0]   eram,
  input logic         u_ram_e,
  input logic [7:0]   pio8255,
  input logic         pio8255_e,
  input logic [7:0]   io,
  input logic         io_e,
  input logic [7:0]   fdc,
  input logic         fdc_e
);
  default clocking cb @(posedge clock_i); endclocking

  // Core golden assertion: D must equal the priority mux evaluation
  property p_mux_truth;
    D == (l_rom_e     ? l_rom   :
          u_rom_e     ? u_rom   :
          u_ram_e     ? eram    :
          ram_e       ? ram     :
          pio8255_e   ? pio8255 :
          io_e        ? io      :
          fdc_e       ? fdc     :
          8'd255);
  endproperty
  assert property (p_mux_truth);

  // Output must never be X/Z at the sample point
  assert property (!$isunknown(D));

  // Default path explicit check
  assert property ((!l_rom_e && !u_rom_e && !u_ram_e && !ram_e && !pio8255_e && !io_e && !fdc_e)
                   |-> D == 8'hFF);

  // Selection coverage (each source and default)
  cover property (l_rom_e && D == l_rom);
  cover property (!l_rom_e && u_rom_e && D == u_rom);
  cover property (!l_rom_e && !u_rom_e && u_ram_e && D == eram);
  cover property (!l_rom_e && !u_rom_e && !u_ram_e && ram_e && D == ram);
  cover property (!l_rom_e && !u_rom_e && !u_ram_e && !ram_e && pio8255_e && D == pio8255);
  cover property (!l_rom_e && !u_rom_e && !u_ram_e && !ram_e && !pio8255_e && io_e && D == io);
  cover property (!l_rom_e && !u_rom_e && !u_ram_e && !ram_e && !pio8255_e && !io_e && fdc_e && D == fdc);
  cover property (!l_rom_e && !u_rom_e && !u_ram_e && !ram_e && !pio8255_e && !io_e && !fdc_e && D == 8'hFF);

  // Conflict coverage: at least one multi-enable case occurs
  cover property (! $onehot0({l_rom_e, u_rom_e, u_ram_e, ram_e, pio8255_e, io_e, fdc_e}));

endmodule

bind dat_i_arbiter dat_i_arbiter_sva sva_inst (
  .clock_i(clock_i),
  .D(D),
  .l_rom(l_rom),
  .l_rom_e(l_rom_e),
  .u_rom(u_rom),
  .u_rom_e(u_rom_e),
  .ram(ram),
  .ram_e(ram_e),
  .eram(eram),
  .u_ram_e(u_ram_e),
  .pio8255(pio8255),
  .pio8255_e(pio8255_e),
  .io(io),
  .io_e(io_e),
  .fdc(fdc),
  .fdc_e(fdc_e)
);