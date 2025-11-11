// SVA checker for selector_mode
module selector_mode_sva
  #(parameter int LO = 2, HI = 5, CLK_CH = 25)
(
    input  logic [31:0] clk,
    input  logic        switch_power,
    input  logic        switch_en,
    input  logic        sig_change,
    input  logic [1:0]  washing_machine_running,
    input  logic        push,
    input  logic [2:0]  sel_value,
    input  logic        init_flag
);

  default clocking cb @(posedge clk[CLK_CH]); endclocking

  let powered   = switch_power;
  let active    = switch_power && !switch_en;
  let en_hold   = switch_power && switch_en;
  let wmr       = washing_machine_running[1];

  function automatic int inc_wrap_i(input int base_i);
    int tmp;
    tmp = (base_i + 1) % (HI+1);
    return (tmp != 0) ? tmp : LO;
  endfunction

  // Range/invariants
  assert property (powered |-> (int'(sel_value) >= LO && int'(sel_value) <= HI));

  // Power-off forces defaults
  assert property (!switch_power |-> (int'(sel_value) == LO && push == 1'b0));

  // Enable hold: sel_value stable, push forced low
  assert property (en_hold |-> ($stable(sel_value) && push == 1'b0));

  // Washing machine running overrides: force LO and push high
  assert property (active && wmr |-> (int'(sel_value) == LO && push == 1'b1));

  // Init clearing when eligible
  assert property ($past(init_flag) && active && !wmr |-> !init_flag);

  // First eligible cycle with init_flag set and no sig_change
  assert property ($past(init_flag) && active && !wmr && !sig_change
                   |-> (int'(sel_value) == LO && push == 1'b0));

  // First eligible cycle with init_flag set and sig_change
  assert property ($past(init_flag) && active && !wmr && sig_change
                   |-> (int'(sel_value) == inc_wrap_i(LO) && push == 1'b1));

  // Normal increment/update on sig_change (after init cleared)
  assert property (active && !wmr && sig_change && !init_flag
                   |-> (push == 1'b1 &&
                        int'(sel_value) == inc_wrap_i(int'($past(sel_value)))));

  // Non-wrap increment
  assert property (active && !wmr && sig_change && !init_flag &&
                   int'($past(sel_value)) >= LO && int'($past(sel_value)) < HI
                   |-> int'(sel_value) == int'($past(sel_value)) + 1);

  // Wrap at HI
  assert property (active && !wmr && sig_change && !init_flag &&
                   int'($past(sel_value)) == HI
                   |-> int'(sel_value) == LO);

  // No-change when no sig_change in normal active state (after init cleared)
  assert property (active && !wmr && !sig_change && !init_flag
                   |-> ($stable(sel_value) && $stable(push)));

  // Push must be low whenever disabled or power-off
  assert property (en_hold |-> push == 1'b0);
  assert property (!switch_power |-> push == 1'b0);

  // Coverage

  // See each legal sel_value while powered
  genvar v;
  generate
    for (v = LO; v <= HI; v++) begin : C_SEEN
      cover property (powered && int'(sel_value) == v);
    end
  endgenerate

  // Cover a wrap event HI -> LO on sig_change
  cover property (active && !wmr && !init_flag &&
                  int'($past(sel_value)) == HI && sig_change ##0 int'(sel_value) == LO);

  // Cover a non-wrap increment
  cover property (active && !wmr && !init_flag &&
                  int'($past(sel_value)) >= LO && int'($past(sel_value)) < HI &&
                  sig_change ##0 int'(sel_value) == int'($past(sel_value)) + 1);

  // Cover washing_machine_running override then a subsequent increment
  cover property (active && wmr ##1 active && !wmr && sig_change &&
                  int'(sel_value) == inc_wrap_i(LO));

  // Cover enable gating and power cycle
  cover property (!switch_power ##1 switch_power);
  cover property (powered && $rose(switch_en));
endmodule

// Bind into DUT
bind selector_mode selector_mode_sva #(.LO(LO), .HI(HI), .CLK_CH(CLK_CH)) u_selector_mode_sva (
  .clk(clk),
  .switch_power(switch_power),
  .switch_en(switch_en),
  .sig_change(sig_change),
  .washing_machine_running(washing_machine_running),
  .push(push),
  .sel_value(sel_value),
  .init_flag(init_flag)
);