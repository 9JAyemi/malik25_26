// SVA for sky130_fd_sc_hd__sdfrtn (negative-edge clocked, sync active-low reset, scan-clear, scan-enable)
module sky130_fd_sc_hd__sdfrtn_sva (
  input logic Q,
  input logic CLK_N,
  input logic D,
  input logic SCD,
  input logic SCE,
  input logic RESET_B
);

  default clocking cb @ (negedge CLK_N); endclocking

  // Track a valid past sample for $past(...)
  logic past_valid;
  initial past_valid = 0;
  always @(negedge CLK_N) past_valid <= 1'b1;

  // Core behavior on each negedge
  // Reset dominates
  assert property ( !RESET_B |-> (Q == 1'b0) )
    else $error("RESET_B low did not clear Q to 0");

  // Synchronous clear via SCD when not in reset
  assert property ( RESET_B && SCD |-> (Q == 1'b0) )
    else $error("SCD asserted did not clear Q to 0");

  // Hold when scan-enable deasserted
  assert property ( disable iff(!past_valid)
                    RESET_B && !SCD && !SCE |-> (Q == $past(Q)) )
    else $error("Q did not hold value when SCE==0");

  // Capture D when scan-enable asserted
  assert property ( disable iff(!past_valid)
                    RESET_B && !SCD && SCE |-> (Q == $past(D)) )
    else $error("Q did not capture D when SCE==1");

  // Q only changes on falling clock edges
  assert property ( $changed(Q) |-> $fell(CLK_N) )
    else $error("Q changed outside a CLK_N falling edge");

  // Q should be a known value at capture edges
  assert property ( !$isunknown(Q) )
    else $error("Q is X/Z on clock edge");

  // Functional coverage (concise but complete)
  // Reset clears
  cover property ( !RESET_B && (Q == 1'b0) );
  // SCD clears (no reset)
  cover property ( RESET_B && SCD && (Q == 1'b0) );
  // Hold path exercised
  cover property ( disable iff(!past_valid)
                   RESET_B && !SCD && !SCE && (Q == $past(Q)) );
  // Capture 0 then 1
  cover property ( disable iff(!past_valid)
                   RESET_B && !SCD && SCE && ($past(D) == 1'b0) && (Q == 1'b0) );
  cover property ( disable iff(!past_valid)
                   RESET_B && !SCD && SCE && ($past(D) == 1'b1) && (Q == 1'b1) );
  // Priority: reset wins over others
  cover property ( !RESET_B && SCD && SCE && (Q == 1'b0) );

endmodule

// Bind into DUT
bind sky130_fd_sc_hd__sdfrtn sky130_fd_sc_hd__sdfrtn_sva u_sva (
  .Q(Q),
  .CLK_N(CLK_N),
  .D(D),
  .SCD(SCD),
  .SCE(SCE),
  .RESET_B(RESET_B)
);