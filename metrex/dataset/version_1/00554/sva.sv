// SVA for d_flip_flop
// Bindable checker focused on concise, high-quality properties

module dff_sva (
  input logic D,
  input logic CLK,
  input logic SET,   // active-low
  input logic RESET, // active-low
  input logic CE,    // active-low disable (CE=1 enables clocked capture)
  input logic Q,
  input logic Q_N
);

  // Use the rising clock as the primary sampling event
  default clocking cb @(posedge CLK); endclocking

  // 1) Output complement must always hold after updates
  a_complement: assert property (1'b1 |-> ##0 (Q_N === ~Q));

  // 2) CE=0: outputs must hold across clock edges
  a_hold_on_clk_when_ce0: assert property ((!CE) |-> ##0 ($stable(Q) && $stable(Q_N)));

  // 3) No change on negedge CE (asynchronous sensitivity but RTL holds)
  a_no_change_on_negedge_ce: assert property (@(negedge CE) ##0 ($stable(Q) && $stable(Q_N)));

  // 4) Priority: SET (active-low) beats RESET and D when CE=1
  a_set_prio:   assert property (CE && (SET==1'b0) |-> ##0 (Q==1'b1 && Q_N==1'b0));

  // 5) RESET (active-low) applies when CE=1 and SET deasserted
  a_reset:      assert property (CE && (SET==1'b1) && (RESET==1'b0) |-> ##0 (Q==1'b0 && Q_N==1'b1));

  // 6) Data capture when CE=1 and both SET/RESET deasserted
  a_data_cap:   assert property (CE && SET && RESET |-> ##0 (Q==D && Q_N==~D));

  // 7) Outputs must be known after any update point
  a_no_x_out:   assert property (1'b1 |-> ##0 !$isunknown({Q,Q_N}));

  // 8) Inputs used synchronously should be known when CE=1
  a_no_x_in_when_used: assert property (CE |-> !$isunknown({D,SET,RESET}));

  // Coverage

  // Data 0->1 propagation under normal capture
  c_data_0_to_1: cover property (SET && RESET && CE && (D==0) ##1 SET && RESET && CE && (D==1));

  // Data 1->0 propagation
  c_data_1_to_0: cover property (SET && RESET && CE && (D==1) ##1 SET && RESET && CE && (D==0));

  // SET dominates when both SET and RESET are low
  c_set_over_reset: cover property (CE && (SET==0) && (RESET==0));

  // RESET alone active
  c_reset_only: cover property (CE && (SET==1) && (RESET==0));

  // CE gating over multiple cycles (hold, then re-enable)
  c_ce_gate_hold_then_enable: cover property ((!CE)[*2] ##1 CE && SET && RESET);

endmodule

// Bind into the DUT
bind d_flip_flop dff_sva u_dff_sva (
  .D(D), .CLK(CLK), .SET(SET), .RESET(RESET), .CE(CE), .Q(Q), .Q_N(Q_N)
);