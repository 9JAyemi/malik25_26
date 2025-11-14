// SVA for controllerHdl_Detect_Change
// Bindable checker focusing on correctness, sequencing, and key coverage.

module controllerHdl_Detect_Change_sva
(
  input  logic                   CLK_IN,
  input  logic                   reset,
  input  logic                   enb_1_2000_0,
  input  logic signed [17:0]     x,
  input  logic                   y,

  // Internal nets for deep checks
  input  logic signed [17:0]     Delay_out1,
  input  logic signed [18:0]     Add_sub_cast,
  input  logic signed [18:0]     Add_sub_cast_1,
  input  logic signed [18:0]     Add_out1,
  input  logic                   Compare_To_Zero2_out1
);

  // 1) Reset and state-update semantics
  // Reset synchronously clears Delay_out1 on the next cycle
  ap_reset_clr: assert property (@(posedge CLK_IN)
    reset |=> (Delay_out1 == 18's0)
  );

  // enb loads x into Delay_out1 on next cycle (when not in reset)
  ap_enb_loads_x: assert property (@(posedge CLK_IN)
    (!reset && enb_1_2000_0) |=> (Delay_out1 == $past(x))
  );

  // Hold value when not enabled (and not in reset)
  ap_hold_when_no_enb: assert property (@(posedge CLK_IN)
    (!reset && !enb_1_2000_0) |=> (Delay_out1 == $past(Delay_out1))
  );

  // Reset dominates enable (clarifies priority)
  ap_reset_dominates: assert property (@(posedge CLK_IN)
    (reset && enb_1_2000_0) |=> (Delay_out1 == 18's0)
  );

  // 2) Combinational correctness of internal nets
  ap_cast_x:  assert property (@(posedge CLK_IN) Add_sub_cast   === $signed(x));
  ap_cast_d:  assert property (@(posedge CLK_IN) Add_sub_cast_1 === $signed(Delay_out1));
  ap_add:     assert property (@(posedge CLK_IN) Add_out1       === (Add_sub_cast - Add_sub_cast_1));
  ap_cmp:     assert property (@(posedge CLK_IN) Compare_To_Zero2_out1 === (Add_out1 != 19's0));

  // Output equivalence
  ap_y_from_cmp: assert property (@(posedge CLK_IN) y === Compare_To_Zero2_out1);

  // End-to-end intent: y flags any change between current x and stored Delay_out1
  ap_y_change_flag: assert property (@(posedge CLK_IN) y === (x != Delay_out1));

  // 3) Behavioral checks under enable (when previous cycle also enabled)
  // If enb was high in consecutive cycles, Delay_out1 equals previous x
  ap_enb_change_sets_y: assert property (@(posedge CLK_IN)
    disable iff (reset)
    (enb_1_2000_0 && $past(enb_1_2000_0) && (x != $past(x))) |-> y
  );
  ap_enb_nochange_clears_y: assert property (@(posedge CLK_IN)
    disable iff (reset)
    (enb_1_2000_0 && $past(enb_1_2000_0) && (x == $past(x))) |-> !y
  );

  // 4) Known-value checks on outputs (post-reset)
  ap_no_x_on_y: assert property (@(posedge CLK_IN)
    disable iff (reset)
    !$isunknown(y)
  );

  // 5) Compact functional coverage
  // Cover: detect change while enabled back-to-back
  cp_change_detect_enb: cover property (@(posedge CLK_IN)
    !reset ##1 (enb_1_2000_0 && $past(enb_1_2000_0) && (x != $past(x)) && y)
  );

  // Cover: no-change while enabled back-to-back
  cp_nochange_enb: cover property (@(posedge CLK_IN)
    !reset ##1 (enb_1_2000_0 && $past(enb_1_2000_0) && (x == $past(x)) && !y)
  );

  // Cover: change detected while enable is low (Delay_out1 held)
  cp_change_while_disabled: cover property (@(posedge CLK_IN)
    !reset ##1 (!enb_1_2000_0 && (x != Delay_out1) && y)
  );

  // Cover: sign-sensitive cases (negative to non-negative transitions while enabled)
  cp_sign_transition: cover property (@(posedge CLK_IN)
    !reset ##1 (enb_1_2000_0 && $past(enb_1_2000_0) && $past(x[17]) && !x[17] && y)
  );

endmodule

// Bind into the DUT to access internals for deep checking
bind controllerHdl_Detect_Change controllerHdl_Detect_Change_sva sva_i (
  .CLK_IN(CLK_IN),
  .reset(reset),
  .enb_1_2000_0(enb_1_2000_0),
  .x(x),
  .y(y),
  .Delay_out1(Delay_out1),
  .Add_sub_cast(Add_sub_cast),
  .Add_sub_cast_1(Add_sub_cast_1),
  .Add_out1(Add_out1),
  .Compare_To_Zero2_out1(Compare_To_Zero2_out1)
);