// SVA for modulo. Bind this to the DUT.
// Focus: functional equivalence, key arithmetic invariants, X-checks, and concise coverage.

module modulo_sva (
  input logic [31:0] A,
  input logic [31:0] B,
  input logic [31:0] C
);

  // Drive a sampling event on any combinational change
  event comb_ev;
  always @* -> comb_ev;
  default clocking cb @(comb_ev); endclocking

  // Functional equivalence to DUT expression (guards avoid % by zero)
  property p_func_eq;
    disable iff ($isunknown({A,B}))
      C == ((B == 32'd0) ? 32'd0
           : ((A == 32'd0) ? 32'd0
             : ((A < 32'd0) ? ((B < 32'd0) ? (-A % -B) : (-A % B))
                             : ((B < 32'd0) ? (A % -B) : (A % B)))));
  endproperty
  assert property (p_func_eq) else $error("modulo: functional mismatch");

  // Zero cases
  assert property (disable iff ($isunknown({A,B})) (B == 32'd0) |-> (C == 32'd0))
    else $error("modulo: B==0 must force C==0");
  assert property (disable iff ($isunknown({A,B})) (B != 32'd0 && A == 32'd0) |-> (C == 32'd0))
    else $error("modulo: A==0 must force C==0");

  // Invariants when B != 0
  assert property (disable iff ($isunknown({A,B})) (B != 32'd0) |-> (C < B))
    else $error("modulo: remainder must be less than divisor (unsigned)");
  assert property (disable iff ($isunknown({A,B})) (B != 32'd0 && A < B) |-> (C == A))
    else $error("modulo: A<B => C==A");
  assert property (disable iff ($isunknown({A,B})) (B != 32'd0 && A == B) |-> (C == 32'd0))
    else $error("modulo: A==B => C==0");
  assert property (disable iff ($isunknown({A,B})) (B == 32'd1) |-> (C == 32'd0))
    else $error("modulo: B==1 => C==0");
  assert property (disable iff ($isunknown({A,B})) (B != 32'd0) |-> (C + B * (A / B) == A))
    else $error("modulo: quotient-remainder identity violated");

  // X/Z checks
  assert property (@cb !$isunknown({A,B})) else $error("modulo: A/B contain X/Z");
  assert property (@cb !$isunknown(C))     else $error("modulo: C contains X/Z");

  // Coverage: exercise key branches/cases (as coded)
  cover property (@cb (B == 32'd0));
  cover property (@cb (B != 32'd0 && A == 32'd0));
  cover property (@cb (B != 32'd0 && A != 32'd0 &&  A < 32'd0 &&  B < 32'd0));
  cover property (@cb (B != 32'd0 && A != 32'd0 &&  A < 32'd0 && !(B < 32'd0)));
  cover property (@cb (B != 32'd0 && A != 32'd0 && !(A < 32'd0) &&  B < 32'd0));
  cover property (@cb (B != 32'd0 && A != 32'd0 && !(A < 32'd0) && !(B < 32'd0)));
  cover property (@cb (B != 32'd0 && A < B));
  cover property (@cb (B != 32'd0 && A == B));
  cover property (@cb (B == 32'd1));
  cover property (@cb (B != 32'd0 && (B & (B - 32'd1)) == 32'd0)); // power-of-two divisor

endmodule

bind modulo modulo_sva u_modulo_sva (.*);