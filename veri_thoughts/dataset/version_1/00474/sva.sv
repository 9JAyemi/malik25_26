// SVA checker for XOR_M
module xor_m_sva (input logic Sgn_X, Sgn_Y, Sgn_Info);

  // Functional equivalence (4-state aware, checked on any change)
  property p_xor_equiv;
    @(Sgn_X or Sgn_Y or Sgn_Info) 1 |-> ##0 (Sgn_Info === (Sgn_X ^ Sgn_Y));
  endproperty
  assert property (p_xor_equiv)
    else $error("XOR_M: Sgn_Info != Sgn_X ^ Sgn_Y");

  // If inputs are known, output must be known and correct (no X/Z leak)
  property p_known_in_known_out;
    @(Sgn_X or Sgn_Y or Sgn_Info)
      ! $isunknown({Sgn_X,Sgn_Y}) |-> ##0 (! $isunknown(Sgn_Info) && (Sgn_Info == (Sgn_X ^ Sgn_Y)));
  endproperty
  assert property (p_known_in_known_out)
    else $error("XOR_M: Known inputs must yield known, correct output");

  // Truth-table coverage
  cover property (@(Sgn_X or Sgn_Y or Sgn_Info) (!Sgn_X && !Sgn_Y && (Sgn_Info==1'b0)));
  cover property (@(Sgn_X or Sgn_Y or Sgn_Info) (!Sgn_X &&  Sgn_Y && (Sgn_Info==1'b1)));
  cover property (@(Sgn_X or Sgn_Y or Sgn_Info) ( Sgn_X && !Sgn_Y && (Sgn_Info==1'b1)));
  cover property (@(Sgn_X or Sgn_Y or Sgn_Info) ( Sgn_X &&  Sgn_Y && (Sgn_Info==1'b0)));

  // Toggle coverage
  cover property (@(Sgn_X)    $rose(Sgn_X));
  cover property (@(Sgn_X)    $fell(Sgn_X));
  cover property (@(Sgn_Y)    $rose(Sgn_Y));
  cover property (@(Sgn_Y)    $fell(Sgn_Y));
  cover property (@(Sgn_Info) $rose(Sgn_Info));
  cover property (@(Sgn_Info) $fell(Sgn_Info));

endmodule

// Bind into DUT
bind XOR_M xor_m_sva u_xor_m_sva (.*);