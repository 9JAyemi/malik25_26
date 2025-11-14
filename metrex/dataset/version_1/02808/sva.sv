// SVA checker for busctrl. Bind this module to the DUT and drive clk/rst_n from TB.
module busctrl_sva
(
  input logic clk, rst_n,

  // DUT ports (as observed by the checker)
  input logic        cpu_en,
  input logic        cpu_wr,
  input logic [1:0]  cpu_size,
  input logic [31:0] cpu_addr,
  input logic [31:0] cpu_data_out,
  input logic [31:0] cpu_data_in,
  input logic        cpu_wt,

  input logic        ram_en,
  input logic        ram_wr,
  input logic [1:0]  ram_size,
  input logic [24:0] ram_addr,
  input logic [31:0] ram_data_in,
  input logic [31:0] ram_data_out,
  input logic        ram_wt,

  input logic        rom_en,
  input logic        rom_wr,
  input logic [1:0]  rom_size,
  input logic [20:0] rom_addr,
  input logic [31:0] rom_data_out,
  input logic        rom_wt,

  input logic        tmr0_en,
  input logic        tmr0_wr,
  input logic [3:2]  tmr0_addr,
  input logic [31:0] tmr0_data_in,
  input logic [31:0] tmr0_data_out,
  input logic        tmr0_wt,

  input logic        tmr1_en,
  input logic        tmr1_wr,
  input logic [3:2]  tmr1_addr,
  input logic [31:0] tmr1_data_in,
  input logic [31:0] tmr1_data_out,
  input logic        tmr1_wt,

  input logic        dsp_en,
  input logic        dsp_wr,
  input logic [13:2] dsp_addr,
  input logic [15:0] dsp_data_in,
  input logic [15:0] dsp_data_out,
  input logic        dsp_wt,

  input logic        kbd_en,
  input logic        kbd_wr,
  input logic        kbd_addr,
  input logic [7:0]  kbd_data_in,
  input logic [7:0]  kbd_data_out,
  input logic        kbd_wt,

  input logic        ser0_en,
  input logic        ser0_wr,
  input logic [3:2]  ser0_addr,
  input logic [7:0]  ser0_data_in,
  input logic [7:0]  ser0_data_out,
  input logic        ser0_wt,

  input logic        ser1_en,
  input logic        ser1_wr,
  input logic [3:2]  ser1_addr,
  input logic [7:0]  ser1_data_in,
  input logic [7:0]  ser1_data_out,
  input logic        ser1_wt,

  input logic        dsk_en,
  input logic        dsk_wr,
  input logic [19:2] dsk_addr,
  input logic [31:0] dsk_data_in,
  input logic [31:0] dsk_data_out,
  input logic        dsk_wt
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n)

  // Address decode replicas
  wire ram_dec  = cpu_en && (cpu_addr[31:29]==3'b000) && (cpu_addr[28:25]==4'b0000);
  wire rom_dec  = cpu_en && (cpu_addr[31:28]==4'b0010) && (cpu_addr[27:21]==7'b0000000);
  wire io_dec   = cpu_en && (cpu_addr[31:28]==4'b0011);
  wire tmr0_dec = io_dec && (cpu_addr[27:20]==8'h00) && (cpu_addr[19:12]==8'h00);
  wire tmr1_dec = io_dec && (cpu_addr[27:20]==8'h00) && (cpu_addr[19:12]==8'h01);
  wire dsp_dec  = io_dec && (cpu_addr[27:20]==8'h01);
  wire kbd_dec  = io_dec && (cpu_addr[27:20]==8'h02);
  wire ser0_dec = io_dec && (cpu_addr[27:20]==8'h03) && (cpu_addr[19:12]==8'h00);
  wire ser1_dec = io_dec && (cpu_addr[27:20]==8'h03) && (cpu_addr[19:12]==8'h01);
  wire dsk_dec  = io_dec && (cpu_addr[27:20]==8'h04);

  wire none_sel = !(ram_en|rom_en|tmr0_en|tmr1_en|dsp_en|kbd_en|ser0_en|ser1_en|dsk_en);

  // Decode correctness and exclusivity
  assert property (ram_en  == ram_dec);
  assert property (rom_en  == rom_dec);
  assert property (tmr0_en == tmr0_dec);
  assert property (tmr1_en == tmr1_dec);
  assert property (dsp_en  == dsp_dec);
  assert property (kbd_en  == kbd_dec);
  assert property (ser0_en == ser0_dec);
  assert property (ser1_en == ser1_dec);
  assert property (dsk_en  == dsk_dec);

  assert property ($onehot0({ram_en,rom_en,tmr0_en,tmr1_en,dsp_en,kbd_en,ser0_en,ser1_en,dsk_en}));

  // Forwarding: write, size, addr, data_in to slaves
  assert property (ram_wr         == cpu_wr);
  assert property (ram_size       == cpu_size);
  assert property (ram_addr       == cpu_addr[24:0]);
  assert property (ram_data_in    == cpu_data_out);

  assert property (rom_wr         == cpu_wr);
  assert property (rom_size       == cpu_size);
  assert property (rom_addr       == cpu_addr[20:0]);

  assert property (tmr0_wr        == cpu_wr);
  assert property (tmr0_addr      == cpu_addr[3:2]);
  assert property (tmr0_data_in   == cpu_data_out);

  assert property (tmr1_wr        == cpu_wr);
  assert property (tmr1_addr      == cpu_addr[3:2]);
  assert property (tmr1_data_in   == cpu_data_out);

  assert property (dsp_wr         == cpu_wr);
  assert property (dsp_addr       == cpu_addr[13:2]);
  assert property (dsp_data_in    == cpu_data_out[15:0]);

  assert property (kbd_wr         == cpu_wr);
  assert property (kbd_addr       == cpu_addr[2]);
  assert property (kbd_data_in    == cpu_data_out[7:0]);

  assert property (ser0_wr        == cpu_wr);
  assert property (ser0_addr      == cpu_addr[3:2]);
  assert property (ser0_data_in   == cpu_data_out[7:0]);

  assert property (ser1_wr        == cpu_wr);
  assert property (ser1_addr      == cpu_addr[3:2]);
  assert property (ser1_data_in   == cpu_data_out[7:0]);

  assert property (dsk_wr         == cpu_wr);
  assert property (dsk_addr       == cpu_addr[19:2]);
  assert property (dsk_data_in    == cpu_data_out);

  // Wait muxing
  assert property (ram_en  |-> cpu_wt == ram_wt);
  assert property (rom_en  |-> cpu_wt == rom_wt);
  assert property (tmr0_en |-> cpu_wt == tmr0_wt);
  assert property (tmr1_en |-> cpu_wt == tmr1_wt);
  assert property (dsp_en  |-> cpu_wt == dsp_wt);
  assert property (kbd_en  |-> cpu_wt == kbd_wt);
  assert property (ser0_en |-> cpu_wt == ser0_wt);
  assert property (ser1_en |-> cpu_wt == ser1_wt);
  assert property (dsk_en  |-> cpu_wt == dsk_wt);
  assert property (none_sel |-> cpu_wt == 1'b1);

  // Read data muxing (incl. zero-extend on narrow slaves) and default
  assert property (ram_en  |-> cpu_data_in == ram_data_out);
  assert property (rom_en  |-> cpu_data_in == rom_data_out);
  assert property (tmr0_en |-> cpu_data_in == tmr0_data_out);
  assert property (tmr1_en |-> cpu_data_in == tmr1_data_out);
  assert property (dsp_en  |-> cpu_data_in == {16'h0000, dsp_data_out});
  assert property (kbd_en  |-> cpu_data_in == {24'h0, kbd_data_out});
  assert property (ser0_en |-> cpu_data_in == {24'h0, ser0_data_out});
  assert property (ser1_en |-> cpu_data_in == {24'h0, ser1_data_out});
  assert property (dsk_en  |-> cpu_data_in == dsk_data_out);
  assert property (none_sel |-> cpu_data_in == 32'h0000_0000);

  // Functional coverage
  cover property (ram_dec  && !cpu_wr);
  cover property (ram_dec  &&  cpu_wr);
  cover property (rom_dec  && !cpu_wr);
  cover property (rom_dec  &&  cpu_wr);
  cover property (tmr0_dec && !cpu_wr);
  cover property (tmr0_dec &&  cpu_wr);
  cover property (tmr1_dec && !cpu_wr);
  cover property (tmr1_dec &&  cpu_wr);
  cover property (dsp_dec  && !cpu_wr);
  cover property (dsp_dec  &&  cpu_wr);
  cover property (kbd_dec  && !cpu_wr);
  cover property (kbd_dec  &&  cpu_wr);
  cover property (ser0_dec && !cpu_wr);
  cover property (ser0_dec &&  cpu_wr);
  cover property (ser1_dec && !cpu_wr);
  cover property (ser1_dec &&  cpu_wr);
  cover property (dsk_dec  && !cpu_wr);
  cover property (dsk_dec  &&  cpu_wr);

  cover property (none_sel && cpu_en); // unmapped access
  cover property (!cpu_en  && none_sel);

  cover property (ram_dec && cpu_size==2'b00);
  cover property (ram_dec && cpu_size==2'b01);
  cover property (ram_dec && cpu_size==2'b10);
  cover property (ram_dec && cpu_size==2'b11);

  cover property (rom_dec && cpu_size==2'b00);
  cover property (rom_dec && cpu_size==2'b01);
  cover property (rom_dec && cpu_size==2'b10);
  cover property (rom_dec && cpu_size==2'b11);

  cover property (ram_en  && ram_wt  && cpu_wt);
  cover property (rom_en  && rom_wt  && cpu_wt);
  cover property (tmr0_en && tmr0_wt && cpu_wt);
  cover property (tmr1_en && tmr1_wt && cpu_wt);
  cover property (dsp_en  && dsp_wt  && cpu_wt);
  cover property (kbd_en  && kbd_wt  && cpu_wt);
  cover property (ser0_en && ser0_wt && cpu_wt);
  cover property (ser1_en && ser1_wt && cpu_wt);
  cover property (dsk_en  && dsk_wt  && cpu_wt);

endmodule

// Example bind (edit clk/rst_n)
// bind busctrl busctrl_sva u_busctrl_sva ( .clk(tb_clk), .rst_n(tb_rst_n),
//   .cpu_en(cpu_en), .cpu_wr(cpu_wr), .cpu_size(cpu_size), .cpu_addr(cpu_addr),
//   .cpu_data_out(cpu_data_out), .cpu_data_in(cpu_data_in), .cpu_wt(cpu_wt),
//   .ram_en(ram_en), .ram_wr(ram_wr), .ram_size(ram_size), .ram_addr(ram_addr),
//   .ram_data_in(ram_data_in), .ram_data_out(ram_data_out), .ram_wt(ram_wt),
//   .rom_en(rom_en), .rom_wr(rom_wr), .rom_size(rom_size), .rom_addr(rom_addr),
//   .rom_data_out(rom_data_out), .rom_wt(rom_wt),
//   .tmr0_en(tmr0_en), .tmr0_wr(tmr0_wr), .tmr0_addr(tmr0_addr),
//   .tmr0_data_in(tmr0_data_in), .tmr0_data_out(tmr0_data_out), .tmr0_wt(tmr0_wt),
//   .tmr1_en(tmr1_en), .tmr1_wr(tmr1_wr), .tmr1_addr(tmr1_addr),
//   .tmr1_data_in(tmr1_data_in), .tmr1_data_out(tmr1_data_out), .tmr1_wt(tmr1_wt),
//   .dsp_en(dsp_en), .dsp_wr(dsp_wr), .dsp_addr(dsp_addr),
//   .dsp_data_in(dsp_data_in), .dsp_data_out(dsp_data_out), .dsp_wt(dsp_wt),
//   .kbd_en(kbd_en), .kbd_wr(kbd_wr), .kbd_addr(kbd_addr),
//   .kbd_data_in(kbd_data_in), .kbd_data_out(kbd_data_out), .kbd_wt(kbd_wt),
//   .ser0_en(ser0_en), .ser0_wr(ser0_wr), .ser0_addr(ser0_addr),
//   .ser0_data_in(ser0_data_in), .ser0_data_out(ser0_data_out), .ser0_wt(ser0_wt),
//   .ser1_en(ser1_en), .ser1_wr(ser1_wr), .ser1_addr(ser1_addr),
//   .ser1_data_in(ser1_data_in), .ser1_data_out(ser1_data_out), .ser1_wt(ser1_wt),
//   .dsk_en(dsk_en), .dsk_wr(dsk_wr), .dsk_addr(dsk_addr),
//   .dsk_data_in(dsk_data_in), .dsk_data_out(dsk_data_out), .dsk_wt(dsk_wt) );