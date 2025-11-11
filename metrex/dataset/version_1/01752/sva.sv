// SVA checker for combinational_circuit
module combinational_circuit_sva #(parameter int W = 50)
(
  input  logic [W-1:0] in,
  input  logic         sel,
  input  logic         out_and,
  input  logic         out_or,
  input  logic         out_xnor
);

  // Functional equivalence checks (disable when inputs unknown)
  assert property ( disable iff ($isunknown({sel,in}))
                    out_and == (sel ? (&in) : 1'b0) );

  assert property ( disable iff ($isunknown({sel,in}))
                    out_or  == (sel ? (|in) : 1'b0) );

  // From the structure: out_xnor is always ~sel (LSB of ~(in ^ ~in))
  assert property ( disable iff ($isunknown(sel))
                    out_xnor == ~sel );

  // Consistency relations
  assert property ( out_and |-> out_or );           // AND implies OR
  assert property ( disable iff ($isunknown({sel,in}))
                    (sel && (out_or==0)) |-> (in=='0) );
  assert property ( disable iff ($isunknown({sel,in}))
                    (sel && (out_and==1)) |-> (&in) );

  // X-propagation sanity: clean inputs => clean outputs
  assert property ( (!$isunknown({sel,in})) |-> (!$isunknown({out_and,out_or,out_xnor})) );

  // Coverage: key functional corners
  cover property ( !sel && out_and==0 && out_or==0 && out_xnor==1 );
  cover property ( sel && (in=='0) && out_and==0 && out_or==0 && out_xnor==0 );
  cover property ( sel && (&in)   && out_and==1 && out_or==1 && out_xnor==0 );
  cover property ( sel && (|in) && ~(&in) && out_and==0 && out_or==1 && out_xnor==0 );
  cover property ( sel && $onehot(in) );

endmodule

// Bind to all instances of combinational_circuit
bind combinational_circuit
  combinational_circuit_sva #(.W(50))
  combinational_circuit_sva_i
  ( .in(in), .sel(sel), .out_and(out_and), .out_or(out_or), .out_xnor(out_xnor) );