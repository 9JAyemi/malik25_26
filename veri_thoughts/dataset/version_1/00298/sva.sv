// SVA for comparator (bindable checker). Concise, full functional checks and coverage.

module comparator_sva #(parameter W=32)
(
  input  logic [W-1:0] a,
  input  logic [W-1:0] b,
  input  logic         unsigned_cmp,
  input  logic         greater,
  input  logic         less,
  input  logic         equal
);

  // Sample on any input change; evaluate after delta to let combinational logic settle
  clocking cb @(a or b or unsigned_cmp); endclocking
  default clocking cb;
  // Ignore checks when any inputs are X/Z
  default disable iff ($isunknown({a,b,unsigned_cmp}));

  // Outputs must always be exactly one-hot (and known)
  assert property (##0 $onehot({greater,less,equal}))
    else $error("comparator onehot violation: g=%0b l=%0b e=%0b", greater,less,equal);

  // Unsigned mode correctness
  assert property (unsigned_cmp |-> ##0
                   (greater == (a > b) && less == (a < b) && equal == (a == b)))
    else $error("comparator unsigned compare mismatch");

  // Signed mode correctness
  assert property (!unsigned_cmp |-> ##0
                   (greater == ($signed(a) > $signed(b)) &&
                    less    == ($signed(a) < $signed(b)) &&
                    equal   == ($signed(a) == $signed(b))))
    else $error("comparator signed compare mismatch");

  // Optional: explicit sign-different branch check in signed mode
  assert property (!unsigned_cmp && (a[31]^b[31]) |-> ##0
                   (greater == !a[31] && less == a[31] && !equal))
    else $error("comparator signed sign-bit branch mismatch");

  // Coverage: all outcomes in both modes
  cover property (unsigned_cmp && (a == b) ##0 equal);
  cover property (unsigned_cmp && (a >  b) ##0 greater);
  cover property (unsigned_cmp && (a <  b) ##0 less);

  cover property (!unsigned_cmp && ($signed(a) == $signed(b)) ##0 equal);
  cover property (!unsigned_cmp && ($signed(a) >  $signed(b)) ##0 greater);
  cover property (!unsigned_cmp && ($signed(a) <  $signed(b)) ##0 less);

  // Coverage: signed-mode sign-bit different paths
  cover property (!unsigned_cmp && (a[31]^b[31]) &&  a[31] ##0 less);
  cover property (!unsigned_cmp && (a[31]^b[31]) && !a[31] ##0 greater);

  // Boundary value coverage
  cover property (!unsigned_cmp && a==32'h8000_0000 && b==32'h0000_0000 ##0 less);
  cover property (!unsigned_cmp && a==32'h7FFF_FFFF && b==32'h8000_0000 ##0 greater);
  cover property ( unsigned_cmp && a==32'hFFFF_FFFF && b==32'h0000_0000 ##0 greater);
  cover property ( unsigned_cmp && a==32'h0000_0000 && b==32'h0000_0000 ##0 equal);

endmodule

// Bind into DUT
bind comparator comparator_sva #(.W(32)) comparator_sva_i (.*);