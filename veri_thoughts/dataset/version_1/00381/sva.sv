// SVA for gatedcap: concise, high-quality checks and coverage
// Bind this file to the DUT: bind gatedcap gatedcap_sva i_gatedcap_sva(.*);

module gatedcap_sva #(
  parameter int unsigned MAXC = 32'd499999,
  parameter int unsigned MAXD = 32'd49999
)(
  input  logic        clk,
  input  logic        rst,
  inout  logic        ld,
  output logic        vcap,
  input  logic [31:0] count,
  input  logic [31:0] discharge_count,
  input  logic [31:0] charge_count,
  input  logic        charging,
  input  logic        discharging
);

  default clocking cb @(posedge clk); endclocking
  // Disable most checks during reset; add explicit reset check below
  default disable iff (rst);

  // Basic invariants
  // ld is driven as charging|discharging
  assert property (cb ld === (charging || discharging))
    else $error("ld must equal charging|discharging");
  // charging and discharging are mutually exclusive
  assert property (cb !(charging && discharging))
    else $error("charging and discharging both asserted");
  // No X on key controls
  assert property (cb !$isunknown({ld, charging, discharging, vcap}))
    else $error("Unknown value on control signal(s)");

  // Reset behavior (synchronous)
  assert property (@(posedge clk) rst |=> (vcap==1'b0 && count==32'd0 &&
                                           discharge_count==32'd0 && charge_count==32'd0 &&
                                           charging==1'b0 && discharging==1'b0))
    else $error("Reset state mismatch");

  // Charging behavior
  // While charging and not at MAXC: increment count, keep discharging deasserted, vcap stable
  assert property (cb charging && (count != MAXC) |=> (charging && !discharging &&
                                                       count == $past(count)+1 && $stable(vcap)))
    else $error("Charging progress/count/vcap stability incorrect");
  // At MAXC: transition to discharging, count resets
  assert property (cb charging && (count == MAXC) |=> (!charging && discharging && count==32'd0))
    else $error("Charging-to-discharging transition incorrect");

  // Discharging behavior
  // When discharging and vcap==0: go idle, clear counters/flags
  assert property (cb discharging && (vcap==1'b0) |=> (!charging && !discharging &&
                                                       count==32'd0 && discharge_count==32'd0 &&
                                                       charge_count==32'd0 && vcap==1'b0))
    else $error("Discharging termination at vcap==0 incorrect");
  // When discharging, vcap!=0, and not at MAXD: increment discharge_count, keep vcap and count stable
  assert property (cb discharging && (vcap!=1'b0) && (discharge_count!=MAXD)
                   |=> (discharging && !charging &&
                        discharge_count == $past(discharge_count)+1 &&
                        $stable(vcap) && $stable(count)))
    else $error("Discharging progress incorrect");
  // When discharging, vcap!=0, and at MAXD: decrement vcap by 1, reset discharge_count; count stable
  assert property (cb discharging && (vcap!=1'b0) && (discharge_count==MAXD)
                   |=> (discharging && !charging &&
                        discharge_count == 32'd0 &&
                        vcap == $past(vcap)-1 &&
                        $stable(count)))
    else $error("Discharging decrement step incorrect");

  // Idle behavior: ld must be low when idle (reinforces ld assignment)
  assert property (cb !charging && !discharging |-> (ld==1'b0))
    else $error("ld not low in idle");

  // vcap never increases (design only decrements or clears)
  assert property (cb !$rose(vcap))
    else $error("vcap rose unexpectedly");

  // charge_count is never used/updated by DUT logic; it must remain stable
  assert property (cb $stable(charge_count))
    else $error("charge_count changed unexpectedly");

  // Coverage
  // See a charge start
  cover property (cb $rose(charging));
  // Observe charge completion and transition to discharging
  cover property (cb charging && (count==MAXC) ##1 discharging);
  // Observe one discharging decrement event
  cover property (cb discharging && (vcap!=1'b0) && (discharge_count==MAXD)
                       ##1 (vcap == $past(vcap)-1));
  // Observe discharging termination when vcap hits zero
  cover property (cb discharging && (vcap==1'b0) ##1 (!charging && !discharging));

  // End-to-end: start charging, eventually transition to discharging
  cover property (cb $rose(charging) ##[1:$] (charging && count==MAXC) ##1 discharging);

endmodule

// Bind example (place outside of module definitions or in your testbench):
// bind gatedcap gatedcap_sva i_gatedcap_sva(.*);