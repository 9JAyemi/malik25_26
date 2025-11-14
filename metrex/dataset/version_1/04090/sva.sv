// SVA for comparator
// Bind this checker to the DUT
bind comparator comparator_sva u_comparator_sva (.A(A), .B(B), .out(out));

module comparator_sva (
  input logic [1:0] A,
  input logic [1:0] B,
  input logic [1:0] out
);
  // Sample on any change; use ##0 in consequents to avoid delta races with combinational logic
  default clocking cb @(A or B or out); endclocking

  // Output legality and known
  assert property (out inside {2'b01,2'b10,2'b11}) else $error("Illegal out encoding");
  assert property (!$isunknown(out)) else $error("out has X/Z");

  // 4-state semantics: unknown A/B force else branch -> out==2'b11
  assert property ( $isunknown({A,B}) |-> ##0 (out==2'b11) )
    else $error("With X/Z on A/B, out must be 2'b11");

  // Functional equivalence for known inputs
  assert property ( !$isunknown({A,B}) |-> ##0
                    ( out == ((A>B) ? 2'b01 :
                              (A<B) ? 2'b10 :
                                      2'b11) ) )
    else $error("Comparator mapping mismatch");

  // Inverse mapping (guards against accidental encoding mix-ups)
  assert property ( (out==2'b01) |-> ##0 (A>B) ) else $error("out=01 implies A>B");
  assert property ( (out==2'b10) |-> ##0 (A<B) ) else $error("out=10 implies A<B");
  assert property ( (out==2'b11) |-> ##0 (A==B) ) else $error("out=11 implies A==B");

  // Coverage: exercise all outcomes
  cover property ( (A>B) ##0 (out==2'b01) );
  cover property ( (A<B) ##0 (out==2'b10) );
  cover property ( (A==B) ##0 (out==2'b11) );
endmodule