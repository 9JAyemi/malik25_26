// SVA checker for karnaugh_map. Bind this to the DUT.
// Uses an input-change sampling event and ##0 to avoid race with combinational update.
module karnaugh_map_sva (
  input logic A, B, C, D,
  input logic F
);

  // Sample on any input edge
  default clocking cb @(
    posedge A or negedge A or
    posedge B or negedge B or
    posedge C or negedge C or
    posedge D or negedge D
  ); endclocking

  // X-prop and functional equivalence (simplified form: F == (A^B) & (C^D))
  property p_func_eq;
    !$isunknown({A,B,C,D}) |-> ##0 (! $isunknown(F) && (F == ((A ^ B) & (C ^ D))));
  endproperty
  assert property (p_func_eq)
    else $error("karnaugh_map: F != (A^B)&(C^D) or X detected");

  // Sanity: F must be 1 on each asserted minterm (post-update)
  assert property ( (A && !B &&  C && !D) |-> ##0 F )
    else $error("karnaugh_map: minterm A!BC!D not driving F=1");
  assert property ( (!A && B && !C &&  D) |-> ##0 F )
    else $error("karnaugh_map: minterm !AB!CD not driving F=1");
  assert property ( (A && !B && !C &&  D) |-> ##0 F )
    else $error("karnaugh_map: minterm A!B!CD not driving F=1");
  assert property ( (!A && B &&  C && !D) |-> ##0 F )
    else $error("karnaugh_map: minterm !AB C!D not driving F=1");

  // Coverage: exercise both output polarities
  cover property ( !$isunknown({A,B,C,D}) |-> ##0 F );
  cover property ( !$isunknown({A,B,C,D}) |-> ##0 !F );

  // Coverage: hit all 4 on-set minterms
  cover property ( ##0 (A && !B &&  C && !D) );
  cover property ( ##0 (!A && B && !C &&  D) );
  cover property ( ##0 (A && !B && !C &&  D) );
  cover property ( ##0 (!A && B &&  C && !D) );

  // Full input-space coverage (compact): SV covergroup
  covergroup cg_inputs @(cb);
    coverpoint {A,B,C,D} { bins all[] = {[0:15]}; }
    coverpoint F;
    cross {A,B,C,D}, F;
  endgroup
  cg_inputs cg = new();

endmodule

// Bind into the DUT
bind karnaugh_map karnaugh_map_sva kmap_sva_i (.A(A), .B(B), .C(C), .D(D), .F(F));