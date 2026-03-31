module dpth_addr_sva (
  input logic        clk,
  input logic        rst_n,
  input logic [7:0]  ir_low,
  input logic [7:0]  rx_low,
  input logic        ld_rat,
  input logic        ld_pc,
  input logic        pc_at,
  input logic [7:0]  m_at,
  // Internal RTL signals (existing in DUT)
  input logic [7:0]  low_sum,
  input logic [7:0]  pc_plus_one,
  input logic [7:0]  rat,
  input logic [7:0]  pc
);
  // Clock: posedge clk; Reset: rst_n active-low async; Logic: mixed (seq rat/pc, comb low_sum/pc_plus_one/m_at mux)

  // During reset, rat and pc are driven to zero.
  reset_regs_zero: assert property (
    @(posedge clk) !rst_n |-> (rat == 8'h00) && (pc == 8'h00)
  );

  // During reset, m_at is zero since it selects between zeroed pc/rat.
  reset_m_at_zero: assert property (
    @(posedge clk) !rst_n |-> (m_at == 8'h00)
  );

  // low_sum equals ir_low + rx_low.
  def_low_sum: assert property (
    @(posedge clk) disable iff (!rst_n) low_sum == (ir_low + rx_low)
  );

  // pc_plus_one equals m_at + 1 (8-bit wraparound).
  def_pc_plus_one: assert property (
    @(posedge clk) disable iff (!rst_n) pc_plus_one == (m_at + 8'd1)
  );

  // m_at is the mux of pc/rat based on pc_at (0 selects pc, 1 selects rat).
  def_m_at_mux: assert property (
    @(posedge clk) disable iff (!rst_n) m_at == ((pc_at == 1'b0) ? pc : rat)
  );

  // When ld_rat is asserted, rat updates to low_sum on the next cycle.
  rat_updates_on_ld: assert property (
    @(posedge clk) disable iff (!rst_n) ld_rat |-> ##1 (rat == $past(low_sum,1,!rst_n))
  );

  // When ld_rat is asserted, pc updates to pc_plus_one on the next cycle.
  pc_updates_on_ld: assert property (
    @(posedge clk) disable iff (!rst_n) ld_rat |-> ##1 (pc == $past(pc_plus_one,1,!rst_n))
  );

  // When ld_rat is deasserted, rat holds its value.
  rat_holds_when_no_ld: assert property (
    @(posedge clk) disable iff (!rst_n) !ld_rat |-> ##1 (rat == $past(rat,1,!rst_n))
  );

  // When ld_rat is deasserted, pc holds its value.
  pc_holds_when_no_ld: assert property (
    @(posedge clk) disable iff (!rst_n) !ld_rat |-> ##1 (pc == $past(pc,1,!rst_n))
  );

  // If ld_rat is asserted and next cycle selects pc, next m_at equals prior m_at + 1.
  m_at_next_is_inc_when_ld_and_pc_sel: assert property (
    @(posedge clk) disable iff (!rst_n) (ld_rat ##1 (pc_at == 1'b0)) |-> (m_at == $past(m_at,1,!rst_n) + 8'd1)
  );

  // If ld_rat is asserted and next cycle selects rat, next m_at equals prior low_sum.
  m_at_next_is_sum_when_ld_and_rat_sel: assert property (
    @(posedge clk) disable iff (!rst_n) (ld_rat ##1 (pc_at == 1'b1)) |-> (m_at == ($past(ir_low,1,!rst_n) + $past(rx_low,1,!rst_n)))
  );

endmodule