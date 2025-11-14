// SVA for pm_clk_real
// Bind into DUT or include inside pm_clk_real
module pm_clk_real_sva;
  // Assume these names are visible via bind into pm_clk_real scope
  // clk, rst, real_speed, rst_counter, irq_n, uart_speed
  // ym_pm, pm_counter, div_cnt, cambio0, cambio1, ultpm

  // Default clocking
  default clocking cb @(posedge clk); endclocking

  // Reset values
  assert property (rst |=> (cambio0==5'd2 && cambio1==5'd4 &&
                            div_cnt==5'd0 && ym_pm==1'b0 &&
                            pm_counter==32'd0 && ultpm==1'b0));

  // Mux mapping (1-cycle latency)
  assert property (disable iff (rst) real_speed              |=> (cambio0==5'd2 && cambio1==5'd4));
  assert property (disable iff (rst) (!real_speed && uart_speed) |=> (cambio0==5'd4 && cambio1==5'd8));
  assert property (disable iff (rst) (!real_speed && !uart_speed)|=> (cambio0==5'd7 && cambio1==5'd15));
  // Sanity: always a valid window
  assert property (disable iff (rst) cambio1 > cambio0);

  // ym_pm/div_cnt behavior
  // Threshold hit -> next cycle set ym_pm=1 and wrap div_cnt to 0
  assert property (disable iff (rst) (div_cnt >= cambio1) |=> (ym_pm && div_cnt==5'd0));
  // Count-up when below threshold
  assert property (disable iff (rst) (div_cnt < cambio1)  |=> (div_cnt == $past(div_cnt)+1));
  // Force low at cambio0
  assert property (disable iff (rst) (div_cnt == cambio0 && div_cnt < cambio1) |=> (ym_pm==1'b0));
  // Hold ym_pm when not at change points
  assert property (disable iff (rst) (div_cnt < cambio1 && div_cnt != cambio0) |=> (ym_pm == $past(ym_pm)));
  // Edge causes
  assert property (disable iff (rst) $rose(ym_pm) |-> ($past(div_cnt >= cambio1) && div_cnt==5'd0));
  assert property (disable iff (rst) $fell(ym_pm) |-> $past(div_cnt == cambio0));

  // ultpm tracks prior ym_pm
  assert property (disable iff (rst) ultpm == $past(ym_pm,1,rst));

  // pm_counter behavior
  // rst_counter dominates
  assert property (disable iff (rst) rst_counter |=> (pm_counter==32'd0));
  // Increment exactly once per rising edge of ym_pm when irq_n and no rst_counter
  assert property (disable iff (rst)
    $past(irq_n && ym_pm && !ultpm && !rst_counter) |-> (pm_counter == $past(pm_counter)+1));
  // No spurious increments
  assert property (disable iff (rst)
    !($past(irq_n && ym_pm && !ultpm) && !$past(rst_counter)) |-> (pm_counter == $past(pm_counter)));

  // Lightweight coverage
  cover property (disable iff (rst) real_speed ##1 (cambio0==5'd2 && cambio1==5'd4));
  cover property (disable iff (rst) (!real_speed && uart_speed) ##1 (cambio0==5'd4 && cambio1==5'd8));
  cover property (disable iff (rst) (!real_speed && !uart_speed) ##1 (cambio0==5'd7 && cambio1==5'd15));
  cover property (disable iff (rst) $rose(ym_pm));
  cover property (disable iff (rst) $fell(ym_pm));
  cover property (disable iff (rst) ($rose(ym_pm) && irq_n && !rst_counter)
                                  ##1 (pm_counter == $past(pm_counter)+1));
  cover property (disable iff (rst) ($rose(ym_pm) && rst_counter) ##1 (pm_counter==32'd0));
endmodule

// Bind into DUT
bind pm_clk_real pm_clk_real_sva sva_inst();