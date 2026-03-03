// SVA checker for OA22X1. Bind this to the DUT.
// Focuses on correctness, X-propagation, power, and concise coverage.
module OA22X1_chk (
  input logic IN1, IN2, IN3, IN4,
  input logic Q,
  input logic VDD, VSS,
  input logic and_out, or_out
);
  // Sample on any input edge
  default clocking cb
    @(posedge IN1 or negedge IN1
    or posedge IN2 or negedge IN2
    or posedge IN3 or negedge IN3
    or posedge IN4 or negedge IN4);
  endclocking

  // Power-good
  wire power_ok = (VDD === 1'b1) && (VSS === 1'b0);
  assume property (power_ok);

  // Partition of select conditions must be exactly one-hot when known
  let c1 =  ( IN1 && !IN2);
  let c2 = (!IN1 &&  IN2);
  let c3 =  ( IN1 &&  IN2);
  let c4 = (!IN1 && !IN2);
  assert property (disable iff (!power_ok)
                   (!$isunknown({IN1,IN2})) |-> $onehot({c1,c2,c3,c4}));

  // Internal nets correctness (when inputs known)
  assert property (disable iff (!power_ok)
                   (!$isunknown({IN3,IN4})) |-> (and_out === (IN3 & IN4)));
  assert property (disable iff (!power_ok)
                   (!$isunknown({IN3,IN4})) |-> (or_out  === (IN3 | IN4)));

  // Functional equivalence (when all inputs known)
  assert property (disable iff (!power_ok)
                   (!$isunknown({IN1,IN2,IN3,IN4})) |->
                   (Q === (( IN1 && !IN2) ? IN3 :
                          ((!IN1 &&  IN2) ? IN4 :
                          (( IN1 &&  IN2) ? (IN3 & IN4) :
                                            (IN3 | IN4))))));

  // No-X on Q when inputs known and power good
  assert property (disable iff (!power_ok)
                   (!$isunknown({IN1,IN2,IN3,IN4})) |-> !$isunknown(Q));

  // Concise functional coverage: exercise each select case
  cover property (power_ok && c1);
  cover property (power_ok && c2);
  cover property (power_ok && c3);
  cover property (power_ok && c4);

  // Propagation covers: when a path is selected, Q follows the driven input(s)
  cover property (power_ok && c1 && $changed(IN3) && (Q === IN3));
  cover property (power_ok && c2 && $changed(IN4) && (Q === IN4));
  cover property (power_ok && c3 && $changed({IN3,IN4})); // AND path exercised
  cover property (power_ok && c4 && $changed({IN3,IN4})); // OR path exercised
endmodule

// Bind into DUT (captures internal wires and_out/or_out)
bind OA22X1 OA22X1_chk u_OA22X1_chk (
  .IN1(IN1), .IN2(IN2), .IN3(IN3), .IN4(IN4), .Q(Q), .VDD(VDD), .VSS(VSS),
  .and_out(and_out), .or_out(or_out)
);