// ram_assertions.sv
// Generic, concise SVA checkers bound to DUTs

// 1-port, registered-address RAM checker
module ram1p_chk #(parameter int W=8, parameter int AW=11) (
  input  logic              clk,
  input  logic              rst,         // active high; tie 0 if none
  input  logic              cap_en,      // address capture enable
  input  logic [AW-1:0]     addr,        // address to capture
  input  logic [AW-1:0]     addr_reg,    // DUT's registered address
  input  logic              wr_en,       // write strobe (already gated)
  input  logic [AW-1:0]     wr_addr,
  input  logic [W-1:0]      din_all,
  input  logic [W-1:0]      dout_all
);
  logic [W-1:0] model [0:(1<<AW)-1];

  always_ff @(posedge clk) if (wr_en) model[wr_addr] <= din_all;

  a_rst_zero:  assert property (@(posedge clk) rst |-> addr_reg == '0);
  a_addr_cap:  assert property (@(posedge clk) disable iff (rst) cap_en  |=> addr_reg == $past(addr));
  a_addr_hold: assert property (@(posedge clk) disable iff (rst) !cap_en |=> addr_reg == $past(addr_reg));
  a_read_data: assert property (@(posedge clk) disable iff (rst) dout_all == model[addr_reg]);

  c_write_read: cover property (@(posedge clk) disable iff (rst) wr_en ##1 (addr_reg == $past(wr_addr) && dout_all == $past(din_all)));
  c_reset:      cover property (@(posedge clk) rst);
endmodule

// 2-port, registered-address RAM checker
module ram2p_chk #(parameter int W=8, parameter int AW=11) (
  input  logic              clka,
  input  logic              rsta,
  input  logic              cap_en_a,
  input  logic [AW-1:0]     addr_a,
  input  logic [AW-1:0]     addr_reg_a,
  input  logic              wr_a,
  input  logic [AW-1:0]     wr_addr_a,
  input  logic [W-1:0]      din_a,
  input  logic [W-1:0]      dout_a,

  input  logic              clkb,
  input  logic              rstb,
  input  logic              cap_en_b,
  input  logic [AW-1:0]     addr_b,
  input  logic [AW-1:0]     addr_reg_b,
  input  logic              wr_b,
  input  logic [AW-1:0]     wr_addr_b,
  input  logic [W-1:0]      din_b,
  input  logic [W-1:0]      dout_b
);
  logic [W-1:0] model [0:(1<<AW)-1];

  always_ff @(posedge clka) if (wr_a) model[wr_addr_a] <= din_a;
  always_ff @(posedge clkb) if (wr_b) model[wr_addr_b] <= din_b;

  a_rst_zero_a:  assert property (@(posedge clka) rsta |-> addr_reg_a == '0);
  a_rst_zero_b:  assert property (@(posedge clkb) rstb |-> addr_reg_b == '0);

  a_addr_cap_a:  assert property (@(posedge clka) disable iff (rsta) cap_en_a  |=> addr_reg_a == $past(addr_a));
  a_addr_cap_b:  assert property (@(posedge clkb) disable iff (rstb) cap_en_b  |=> addr_reg_b == $past(addr_b));
  a_addr_hold_a: assert property (@(posedge clka) disable iff (rsta) !cap_en_a |=> addr_reg_a == $past(addr_reg_a));
  a_addr_hold_b: assert property (@(posedge clkb) disable iff (rstb) !cap_en_b |=> addr_reg_b == $past(addr_reg_b));

  a_read_data_a: assert property (@(posedge clka) disable iff (rsta) dout_a == model[addr_reg_a]);
  a_read_data_b: assert property (@(posedge clkb) disable iff (rstb) dout_b == model[addr_reg_b]);

  c_a_write_a_read: cover property (@(posedge clka) disable iff (rsta) wr_a ##1 (addr_reg_a == $past(wr_addr_a) && dout_a == $past(din_a)));
  c_b_write_b_read: cover property (@(posedge clkb) disable iff (rstb) wr_b ##1 (addr_reg_b == $past(wr_addr_b) && dout_b == $past(din_b)));
  c_same_addr_collision: cover property (@(posedge clka) wr_a && wr_b && (wr_addr_a == wr_addr_b));
endmodule

// 1W2R async-read distributed RAM checker
module ram1w2r_async_chk #(parameter int W=1, parameter int AW=5) (
  input  logic              wclk,
  input  logic              we,
  input  logic [AW-1:0]     wa,
  input  logic [W-1:0]      din,
  input  logic [AW-1:0]     a,
  input  logic [AW-1:0]     dpra,
  input  logic [W-1:0]      spo,
  input  logic [W-1:0]      dpo
);
  logic [W-1:0] model [0:(1<<AW)-1];

  always_ff @(posedge wclk) if (we) model[wa] <= din;

  a_read_matches_a:    assert property (@(posedge wclk) spo == model[a]);
  a_read_matches_dpra: assert property (@(posedge wclk) dpo == model[dpra]);

  c_write_seen_on_spo: cover property (@(posedge wclk) we && (a    == wa));
  c_write_seen_on_dpo: cover property (@(posedge wclk) we && (dpra == wa));
endmodule

// Binds

bind lpm_ram_dq ram1p_chk #(.W(lpm_width), .AW(lpm_widthad)) lpm_ram_dq_chk (
  .clk(inclock),
  .rst(1'b0),
  .cap_en(1'b1),
  .addr(address),
  .addr_reg(addr_reg),
  .wr_en(we),
  .wr_addr(address),
  .din_all(data),
  .dout_all(q)
);

bind altqpram ram2p_chk #(.W(width_write_a), .AW(widthad_write_a)) altqpram_chk (
  .clka(inclock_a),
  .rsta(inaclr_a),
  .cap_en_a(inclocken_a),
  .addr_a(wraddress_a),
  .addr_reg_a(addr_reg_a),
  .wr_a(inclocken_a && wren_a),
  .wr_addr_a(wraddress_a),
  .din_a(data_a),
  .dout_a(q_a),

  .clkb(inclock_b),
  .rstb(inaclr_b),
  .cap_en_b(inclocken_b),
  .addr_b(wraddress_b),
  .addr_reg_b(addr_reg_b),
  .wr_b(inclocken_b && wren_b),
  .wr_addr_b(wraddress_b),
  .din_b(data_b),
  .dout_b(q_b)
);

bind RAMB16_S36_S36 ram2p_chk #(.W(32+4), .AW(9)) ramb16_s36_s36_chk (
  .clka(CLKA),
  .rsta(SSRA),
  .cap_en_a(ENA),
  .addr_a(ADDRA),
  .addr_reg_a(addr_reg_a),
  .wr_a(ENA && WEA),
  .wr_addr_a(ADDRA),
  .din_a({DIPA, DIA}),
  .dout_a({DOPA, DOA}),

  .clkb(CLKB),
  .rstb(SSRB),
  .cap_en_b(ENB),
  .addr_b(ADDRB),
  .addr_reg_b(addr_reg_b),
  .wr_b(ENB && WEB),
  .wr_addr_b(ADDRB),
  .din_b({DIPB, DIB}),
  .dout_b({DOPB, DOB})
);

bind RAMB16_S9 ram1p_chk #(.W(8+1), .AW(11)) ramb16_s9_chk (
  .clk(CLK),
  .rst(SSR),
  .cap_en(EN),
  .addr(ADDR),
  .addr_reg(addr_reg),
  .wr_en(EN && WE),
  .wr_addr(ADDR),
  .din_all({DIP, DI}),
  .dout_all({DOP, DO})
);

bind RAMB16_S36 ram1p_chk #(.W(32+4), .AW(9)) ramb16_s36_chk (
  .clk(CLK),
  .rst(SSR),
  .cap_en(EN),
  .addr(ADDR),
  .addr_reg(addr_reg),
  .wr_en(EN && WE),
  .wr_addr(ADDR),
  .din_all({DIP, DI}),
  .dout_all({DOP, DO})
);

bind RAMB16_S18 ram1p_chk #(.W(16+2), .AW(10)) ramb16_s18_chk (
  .clk(CLK),
  .rst(SSR),
  .cap_en(EN),
  .addr(ADDR),
  .addr_reg(addr_reg),
  .wr_en(EN && WE),
  .wr_addr(ADDR),
  .din_all({DIP, DI}),
  .dout_all({DOP, DO})
);

bind RAMB4_S16_S16 ram2p_chk #(.W(16), .AW(8)) ramb4_s16_s16_chk (
  .clka(CLKA),
  .rsta(RSTA),
  .cap_en_a(ENA),
  .addr_a(ADDRA),
  .addr_reg_a(addr_reg_a),
  .wr_a(ENA && WEA),
  .wr_addr_a(ADDRA),
  .din_a(DIA),
  .dout_a(DOA),

  .clkb(CLKB),
  .rstb(RSTB),
  .cap_en_b(ENB),
  .addr_b(ADDRB),
  .addr_reg_b(addr_reg_b),
  .wr_b(ENB && WEB),
  .wr_addr_b(ADDRB),
  .din_b(DIB),
  .dout_b(DOB)
);

bind RAMB4_S4 ram1p_chk #(.W(4), .AW(10)) ramb4_s4_chk (
  .clk(CLK),
  .rst(RST),
  .cap_en(EN),
  .addr(ADDR),
  .addr_reg(addr_reg),
  .wr_en(EN && WE),
  .wr_addr(ADDR),
  .din_all(DI),
  .dout_all(DO)
);

bind RAMB4_S16 ram1p_chk #(.W(16), .AW(8)) ramb4_s16_chk (
  .clk(CLK),
  .rst(RST),
  .cap_en(EN),
  .addr(ADDR),
  .addr_reg(addr_reg),
  .wr_en(EN && WE),
  .wr_addr(ADDR),
  .din_all(DI),
  .dout_all(DO)
);

bind RAMB4_S2 ram1p_chk #(.W(2), .AW(11)) ramb4_s2_chk (
  .clk(CLK),
  .rst(RST),
  .cap_en(EN),
  .addr(ADDR),
  .addr_reg(addr_reg),
  .wr_en(EN && WE),
  .wr_addr(ADDR),
  .din_all(DI),
  .dout_all(DO)
);

bind RAMB4_S8 ram1p_chk #(.W(8), .AW(9)) ramb4_s8_chk (
  .clk(CLK),
  .rst(RST),
  .cap_en(EN),
  .addr(ADDR),
  .addr_reg(addr_reg),
  .wr_en(EN && WE),
  .wr_addr(ADDR),
  .din_all(DI),
  .dout_all(DO)
);

bind RAM32X1D ram1w2r_async_chk #(.W(1), .AW(5)) ram32x1d_chk (
  .wclk(WCLK),
  .we(WE),
  .wa({A4,A3,A2,A1,A0}),
  .din(D),
  .a({A4,A3,A2,A1,A0}),
  .dpra({DPRA4,DPRA3,DPRA2,DPRA1,DPRA0}),
  .spo(SPO),
  .dpo(DPO)
);

bind RAM16X1D ram1w2r_async_chk #(.W(1), .AW(4)) ram16x1d_chk (
  .wclk(WCLK),
  .we(WE),
  .wa({A3,A2,A1,A0}),
  .din(D),
  .a({A3,A2,A1,A0}),
  .dpra({DPRA3,DPRA2,DPRA1,DPRA0}),
  .spo(SPO),
  .dpo(DPO)
);