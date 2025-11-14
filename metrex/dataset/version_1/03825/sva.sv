// SVA for RFID. Bind this file to the DUT.
// Assumes IEEE 1800-2017 sampling (values checked at posedge before NBAs take effect).

module RFID_sva #(parameter int n = 8, k = 4)
(
  input logic                 clk,
  input logic                 rst,
  input logic [n-1:0]         data_in,
  input logic                 start,
  input logic [k-1:0]         tx,
  // tap internal regs
  input logic [n-1:0]         data_reg,
  input logic [3:0]           count,
  input logic                 start_reg
);

  // Parameter sanity (count is 4 bits wide)
  initial assert (k >= 1 && k <= 16)
    else $error("RFID: parameter k (%0d) must be in [1..16] to fit 4-bit count", k);

  // Basic 2-state cleanliness and range
  property p_no_x;
    @(posedge clk) disable iff (rst)
      !$isunknown({start_reg, count, tx});
  endproperty
  a_no_x: assert property(p_no_x);

  property p_count_range;
    @(posedge clk) disable iff (rst)
      count <= k-1;
  endproperty
  a_count_range: assert property(p_count_range);

  property p_tx_value_range;
    @(posedge clk) disable iff (rst)
      tx <= 'd1; // tx is only 0 or 1
  endproperty
  a_tx_value_range: assert property(p_tx_value_range);

  // Reset effects (next cycle)
  property p_reset_clears;
    @(posedge clk) rst |=> (count == 0 && tx == '0 && !start_reg);
  endproperty
  a_reset_clears: assert property(p_reset_clears);

  // Start branch (accepted immediately)
  property p_start_accepts;
    @(posedge clk) disable iff (rst)
      start |=> (start_reg && count == 0 && tx == 'd1 && data_reg == $past(data_in));
  endproperty
  a_start_accepts: assert property(p_start_accepts);

  // Mid-burst step (no overlapping start): increment, keep busy, tx=0
  property p_mid_burst_step;
    @(posedge clk) disable iff (rst)
      ($past(start_reg) && !$past(start) && $past(count) < k-1)
        |=> (start_reg && count == $past(count) + 1 && tx == '0);
  endproperty
  a_mid_burst_step: assert property(p_mid_burst_step);

  // Final-burst step (no overlapping start): complete, deassert busy, tx=1
  property p_final_burst_step;
    @(posedge clk) disable iff (rst)
      ($past(start_reg) && !$past(start) && $past(count) == k-1)
        |=> (!start_reg && count == 0 && tx == 'd1);
  endproperty
  a_final_burst_step: assert property(p_final_burst_step);

  // Idle step (no start, not busy): remain idle, tx=0
  property p_idle_step;
    @(posedge clk) disable iff (rst)
      (!$past(start) && !$past(start_reg))
        |=> (!start_reg && tx == '0);
  endproperty
  a_idle_step: assert property(p_idle_step);

  // Data register only updates on start; otherwise holds
  property p_data_reg_hold;
    @(posedge clk) disable iff (rst)
      !start |=> data_reg == $past(data_reg);
  endproperty
  a_data_reg_hold: assert property(p_data_reg_hold);

  // Causality on tx: any tx==1 must come from start or finalization in prior cycle
  property p_tx_one_cause;
    @(posedge clk) disable iff (rst)
      (tx == 'd1) |-> ($past(start) || ($past(start_reg) && $past(count) == k-1));
  endproperty
  a_tx_one_cause: assert property(p_tx_one_cause);

  // Full-burst coverage (no overlap): 1 then k-1 zeros then 1, then idle
  cover property (@(posedge clk) disable iff (rst)
    start ##1 (tx == 'd1)
      ##1 (tx == '0 && !start) [* (k-1)]
      ##1 (tx == 'd1)
      ##1 (!start_reg)
  );

  // Overlapping start coverage: start during busy causes immediate restart (tx=1, count=0)
  cover property (@(posedge clk) disable iff (rst)
    start ##1 start_reg ##[1:$] (start && start_reg)
      ##1 (tx == 'd1 && count == 0 && start_reg)
  );

  // Reset-and-idle coverage
  cover property (@(posedge clk)
    rst ##1 (!rst && count == 0 && tx == '0 && !start_reg)
  );

endmodule

// Bind to the DUT
bind RFID RFID_sva #(.n(n), .k(k)) RFID_sva_i (
  .clk(clk), .rst(rst), .data_in(data_in), .start(start), .tx(tx),
  .data_reg(data_reg), .count(count), .start_reg(start_reg)
);