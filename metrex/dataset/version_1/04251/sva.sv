// SVA for jt51_timer and jt51_timers
// Focused, high-quality checks and concise coverage

// Per-instance timer SVA
module jt51_timer_sva #(parameter int CW=8, FREE_EN=0)
(
  input  logic              clk,
  input  logic              rst,
  input  logic              cen,
  input  logic              zero,
  input  logic [CW-1:0]     start_value,
  input  logic              load,
  input  logic              clr_flag,
  input  logic              flag,
  input  logic              overflow,
  // internal state taps
  input  logic [CW-1:0]     cnt,
  input  logic [CW-1:0]     next,
  input  logic              last_load,
  input  logic [3:0]        free_cnt
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Helpers
  let inc       = (FREE_EN ? (free_cnt==4'hF) : 1'b1);
  let sum       = {1'b0, cnt} + inc;
  let prev_last = $past(last_load, 1, 1'b0);
  let load_rise = load && !prev_last;

  // Asynchronous flag reset must immediately clear
  assert property (disable iff (1'b0) @(posedge rst) flag==1'b0);

  // Combinational next/overflow must match adder model
  assert property (1'b1 |-> {overflow, next} == sum);

  // free_cnt behavior
  assert property (rst |=> free_cnt==4'd0);
  assert property ((cen && zero) |=> free_cnt == $past(free_cnt)+4'd1);
  assert property (!(cen && zero) |=> free_cnt == $past(free_cnt));

  // last_load sampling only when cen&&zero
  assert property ((cen && zero) |=> last_load == $past(load));
  assert property (!(cen && zero) |=> last_load == $past(last_load));

  // Counter update rules when cen&&zero
  assert property ((cen && zero) && (load_rise || overflow) |=> cnt == $past(start_value));
  assert property ((cen && zero) && !load_rise && !overflow && prev_last |=> cnt == $past(next));
  assert property ((cen && zero) && !load_rise && !overflow && !prev_last |=> cnt == $past(cnt));
  // Hold when not enabled
  assert property (!(cen && zero) |=> cnt == $past(cnt));

  // Flag set/clear/hold
  assert property (clr_flag |=> flag==1'b0);
  assert property (!clr_flag && overflow |=> flag==1'b1);
  assert property (flag && !clr_flag |=> flag==1'b1);

  // FREE_EN specific strengthening
  if (FREE_EN) begin
    assert property ((free_cnt!=4'hF) |-> (overflow==1'b0 && next==cnt));
    assert property ((free_cnt==4'hF) |-> {overflow,next} == {1'b0,cnt} + 1'b1);
  end else begin
    assert property (1'b1 |-> next == cnt + 1'b1);
  end

  // Minimal, meaningful coverage
  cover property ((cen && zero) && load_rise |=> cnt == $past(start_value));
  cover property ((FREE_EN ? (free_cnt==4'hF) : 1'b1) && (&cnt) |-> overflow);
  cover property (overflow && !clr_flag ##1 flag ##1 clr_flag ##1 !flag);

endmodule


// Top-level timers SVA
module jt51_timers_sva
(
  input  logic clk,
  input  logic rst,
  input  logic flag_A,
  input  logic flag_B,
  input  logic enable_irq_A,
  input  logic enable_irq_B,
  input  logic irq_n
);
  default clocking @(posedge clk); endclocking

  // IRQ function must match Boolean definition
  assert property (irq_n == ~((flag_A && enable_irq_A) || (flag_B && enable_irq_B)));

  // Minimal coverage: each source pulls IRQ low, and both
  cover property ((flag_A && enable_irq_A) ##0 !irq_n);
  cover property ((flag_B && enable_irq_B) ##0 !irq_n);
  cover property ((flag_A && enable_irq_A) && (flag_B && enable_irq_B) ##0 !irq_n);

endmodule


// Binds
bind jt51_timer
  jt51_timer_sva #(.CW(CW), .FREE_EN(FREE_EN)) u_timer_sva
  (
    .clk        (clk),
    .rst        (rst),
    .cen        (cen),
    .zero       (zero),
    .start_value(start_value),
    .load       (load),
    .clr_flag   (clr_flag),
    .flag       (flag),
    .overflow   (overflow),
    .cnt        (cnt),
    .next       (next),
    .last_load  (last_load),
    .free_cnt   (free_cnt)
  );

bind jt51_timers
  jt51_timers_sva u_timers_sva
  (
    .clk          (clk),
    .rst          (rst),
    .flag_A       (flag_A),
    .flag_B       (flag_B),
    .enable_irq_A (enable_irq_A),
    .enable_irq_B (enable_irq_B),
    .irq_n        (irq_n)
  );