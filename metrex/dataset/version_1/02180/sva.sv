// SVA for d_ff_scd_sce
// Bindable, concise, high-quality checks and coverage

module d_ff_scd_sce_sva (
  input logic CLK,
  input logic D,
  input logic SCD,
  input logic SCE,
  input logic Q,
  input logic Q_N
);

  // track $past validity
  logic past_valid;
  initial past_valid = 1'b0;
  always @(posedge CLK) past_valid <= 1'b1;

  // 1) Complement always holds (sampled on clk edges)
  assert property (@(posedge CLK) past_valid |-> (Q_N === ~Q))
    else $error("Q_N not complement of Q");

  // 2) SCD has priority: on next edge Q=0, Q_N=1
  assert property (@(posedge CLK) past_valid && $past(SCD) |-> (Q === 1'b0 && Q_N === 1'b1))
    else $error("SCD path violated");

  // 3) SCE load when SCD=0: on next edge Q=D, Q_N=~D
  assert property (@(posedge CLK) past_valid && !$past(SCD) && $past(SCE)
                   |-> (Q === $past(D) && Q_N === $past(~D)))
    else $error("SCE load path violated");

  // 4) Hold when SCD=0 and SCE=0: outputs stable across cycle
  assert property (@(posedge CLK) past_valid && !$past(SCD) && !$past(SCE)
                   |-> (Q === $past(Q) && Q_N === $past(Q_N)))
    else $error("Hold behavior violated");

  // 5) Output change implies an enable (SCD or SCE) in prior cycle
  assert property (@(posedge CLK) past_valid &&
                   ((Q !== $past(Q)) || (Q_N !== $past(Q_N)))
                   |-> $past(SCD || SCE))
    else $error("Output changed without enable");

  // 6) No mid-cycle glitches (stable at negedge)
  assert property (@(negedge CLK) $stable(Q) && $stable(Q_N))
    else $error("Glitch detected between clock edges");

  // Functional coverage
  cover property (@(posedge CLK) past_valid && $past(SCD));                           // SCD asserted
  cover property (@(posedge CLK) past_valid && $past(SCD && SCE));                    // Priority case (both high)
  cover property (@(posedge CLK) past_valid && !$past(SCD) && $past(SCE) && ($past(D)==1'b0)); // Load 0
  cover property (@(posedge CLK) past_valid && !$past(SCD) && $past(SCE) && ($past(D)==1'b1)); // Load 1
  cover property (@(posedge CLK) past_valid && !$past(SCD) && !$past(SCE));           // Hold case
  cover property (@(posedge CLK) past_valid && $past(SCE) && !$past(SCD) &&
                  (Q !== $past(Q)));                                                  // Q toggled under SCE

endmodule

// Bind to DUT
bind d_ff_scd_sce d_ff_scd_sce_sva u_d_ff_scd_sce_sva (
  .CLK(CLK), .D(D), .SCD(SCD), .SCE(SCE), .Q(Q), .Q_N(Q_N)
);