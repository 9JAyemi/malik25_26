// SVA checker for LCDDisplay
// Bind this module to the DUT:  bind LCDDisplay LCDDisplay_sva sva();

module LCDDisplay_sva (LCDDisplay dut);

  // Local encodings (mirror DUT)
  localparam bit       IDLE = 1'b0, BUSY = 1'b1;
  localparam [2:0]     NOP  = 3'b000, K0 = 3'b100, K1 = 3'b101, K2 = 3'b110, K3 = 3'b111;
  localparam int       EN_PW = 20;
  localparam int       CLR_END = 8000;
  localparam int       WRT_END = 250;

  // Start checking after first clock edge
  bit init_done;
  initial init_done = 1'b0;
  always @(negedge dut.clk_i) init_done <= 1'b1;

  default clocking cb @(negedge dut.clk_i); endclocking
  default disable iff (!init_done);

  // Global sanity
  assert property (dut.state == IDLE |-> (!dut.en_o && dut.lcd_clr_state==2'b00 && dut.lcd_wrt_state==3'b000));
  assert property (dut.state == BUSY |-> ((dut.lcd_clr_state!=2'b00) ^ (dut.lcd_wrt_state!=3'b000)));
  assert property (!(dut.func_o_0!=2'b00 && dut.func_o_1!=2'b00));
  assert property ($rose(dut.en_o) |-> dut.state==BUSY);
  assert property ($rose(dut.en_o) |=> dut.en_o[*EN_PW] ##1 !dut.en_o);

  // IDLE command handling
  assert property (dut.state==IDLE && (dut.func_i inside {NOP,K1,K3}) |=> dut.state==IDLE);

  // K0 (clear) accept -> BUSY and clear engine start
  assert property (dut.state==IDLE && dut.func_i==K0
                   |=> dut.state==BUSY && dut.lcd_clr_state==2'b10 && dut.lcd_clr_cyc==0 &&
                       dut.en_o && dut.func_o_0==2'b00 && dut.data_o_0==8'h01 && dut.lcd_wrt_state==3'b000);

  // Clear pulse/length and completion
  assert property (dut.lcd_clr_state==2'b10 && dut.lcd_clr_cyc < EN_PW  |-> dut.en_o);
  assert property (dut.lcd_clr_state==2'b10 && dut.lcd_clr_cyc == EN_PW |-> !dut.en_o);
  assert property (dut.lcd_clr_state==2'b10 && dut.lcd_clr_cyc > EN_PW  |-> !dut.en_o);
  assert property (dut.lcd_clr_state==2'b10 && dut.lcd_clr_cyc < CLR_END |=> dut.lcd_clr_cyc == $past(dut.lcd_clr_cyc)+1);
  assert property (dut.lcd_clr_state==2'b10 && dut.lcd_clr_cyc == CLR_END
                   |=> dut.lcd_clr_state==2'b00 && dut.state==IDLE && dut.func_o_0==2'b00 && dut.data_o_0==8'h00);

  // K2 (write burst) accept -> BUSY and write engine start
  assert property (dut.state==IDLE && dut.func_i==K2
                   |=> dut.state==BUSY && dut.lcd_wrt_state==3'b001 && dut.cursor_pos==0 && dut.ddram_addr==7'h00 && dut.lcd_clr_state==2'b00);

  // K2 loads/rolls data_c
  genvar gi;
  generate
    for (gi=0; gi<16; gi++) begin : g_load
      assert property (dut.state==IDLE && dut.func_i==K2
                       |=> dut.data_c[gi] == $past(dut.data_i[8*gi +: 8]));
      assert property (dut.state==IDLE && dut.func_i==K2
                       |=> dut.data_c[gi+16] == $past(dut.data_c[gi]));
    end
  endgenerate

  // Address phase outputs and transition
  assert property (dut.lcd_wrt_state==3'b001 && dut.ddram_addr!=7'h50
                   |-> dut.en_o && dut.func_o_1==2'b00 && dut.data_o_1=={1'b1, dut.ddram_addr});
  assert property (dut.lcd_wrt_state==3'b001 && dut.ddram_addr!=7'h50
                   |=> dut.lcd_wrt_state==3'b010 && dut.lcd_wrt_cyc==0);

  // Address counter update (incl wrap at 0x0F -> 0x40) and done at 0x50
  assert property (dut.lcd_wrt_state==3'b001 && dut.ddram_addr!=7'h50 && dut.ddram_addr!=7'h0F
                   |=> dut.ddram_addr == $past(dut.ddram_addr) + 7'h01);
  assert property (dut.lcd_wrt_state==3'b001 && dut.ddram_addr==7'h0F
                   |=> dut.ddram_addr == 7'h40);
  assert property (dut.lcd_wrt_state==3'b001 && dut.ddram_addr==7'h50
                   |-> dut.cursor_pos==32);
  assert property (dut.lcd_wrt_state==3'b001 && dut.ddram_addr==7'h50
                   |=> dut.lcd_wrt_state==3'b000 && dut.state==IDLE && dut.func_o_1==2'b00 && dut.data_o_1==8'h00);

  // 010 wait: exact length, EN pulse width, counter monotonic
  assert property (dut.lcd_wrt_state==3'b010 && dut.lcd_wrt_cyc==0
                   |-> (dut.lcd_wrt_state==3'b010)[*251] ##1 (dut.lcd_wrt_state==3'b011 && dut.lcd_wrt_cyc==0));
  assert property (dut.lcd_wrt_state==3'b010 && dut.lcd_wrt_cyc < WRT_END |=> dut.lcd_wrt_cyc == $past(dut.lcd_wrt_cyc)+1);
  assert property (dut.lcd_wrt_state==3'b010 && dut.lcd_wrt_cyc < EN_PW  |-> dut.en_o);
  assert property (dut.lcd_wrt_state==3'b010 && dut.lcd_wrt_cyc >= EN_PW |-> !dut.en_o);

  // Data phase outputs and transition
  assert property (dut.lcd_wrt_state==3'b011
                   |-> dut.en_o && dut.func_o_1==2'b10 && dut.data_o_1==dut.data_c[dut.cursor_pos]);
  assert property (dut.lcd_wrt_state==3'b011
                   |=> dut.lcd_wrt_state==3'b100 && dut.lcd_wrt_cyc==0 && dut.cursor_pos == $past(dut.cursor_pos)+1);

  // 100 wait: exact length, EN pulse width, counter monotonic
  assert property (dut.lcd_wrt_state==3'b100 && dut.lcd_wrt_cyc==0
                   |-> (dut.lcd_wrt_state==3'b100)[*251] ##1 (dut.lcd_wrt_state==3'b001));
  assert property (dut.lcd_wrt_state==3'b100 && dut.lcd_wrt_cyc < WRT_END |=> dut.lcd_wrt_cyc == $past(dut.lcd_wrt_cyc)+1);
  assert property (dut.lcd_wrt_state==3'b100 && dut.lcd_wrt_cyc < EN_PW  |-> dut.en_o);
  assert property (dut.lcd_wrt_state==3'b100 && dut.lcd_wrt_cyc >= EN_PW |-> !dut.en_o);

  // Coverage
  cover property (dut.state==IDLE && dut.func_i==K0 ##1
                  dut.lcd_clr_state==2'b10 && dut.lcd_clr_cyc==0 ##[1:$]
                  dut.lcd_clr_state==2'b10 && dut.lcd_clr_cyc==CLR_END ##1 dut.state==IDLE);
  cover property (dut.state==IDLE && dut.func_i==K2 ##1
                  dut.lcd_wrt_state==3'b001 && dut.ddram_addr==7'h00 ##[1:$]
                  dut.lcd_wrt_state==3'b001 && dut.ddram_addr==7'h0F ##1 dut.ddram_addr==7'h40 ##[1:$]
                  dut.lcd_wrt_state==3'b011 && dut.cursor_pos==31 ##1
                  dut.lcd_wrt_state==3'b001 && dut.ddram_addr==7'h50 ##1 dut.state==IDLE);
  cover property ($rose(dut.en_o) ##EN_PW !dut.en_o);

endmodule