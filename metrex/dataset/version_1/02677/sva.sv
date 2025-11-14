// SVA checker for multi_input_module
// Focus: concise, high-quality functional equivalence, directional checks, and key coverage
// synopsys translate_off
module multi_input_module_sva (
  input logic a,b,c,d,e,f,g,h,i,
  input logic out
);

  // Sample on any input transition
  default clocking cb @(
    posedge a or negedge a or
    posedge b or negedge b or
    posedge c or negedge c or
    posedge d or negedge d or
    posedge e or negedge e or
    posedge f or negedge f or
    posedge g or negedge g or
    posedge h or negedge h or
    posedge i or negedge i
  ); endclocking

  // Shorthand terms
  function automatic logic any_term;
    any_term = (a & b) | (c | d) | ~(e | f) | g | ~h | i;
  endfunction

  // Functional equivalence (strongest single check)
  assert property ( out == any_term )
    else $error("out != (a&b)|(c|d)|~(e|f)|g|~h|i");

  // Directional checks (helpful pinpointing)
  assert property ( (a & b) |-> out );
  assert property ( (c | d) |-> out );
  assert property ( ~(e | f) |-> out );
  assert property ( g |-> out );
  assert property ( (~h) |-> out );
  assert property ( i |-> out );

  // No-false-positive: if all terms false, out must be 0
  assert property ( (! (a & b)) && (! (c | d)) && (e | f) && (!g) && h && (!i) |-> !out );

  // Clean value check: known inputs imply known output
  assert property ( !$isunknown({a,b,c,d,e,f,g,h,i}) |-> !$isunknown(out) );

  // Basic coverage: out can be 0 and 1; it can toggle
  cover property ( out == 0 );
  cover property ( out == 1 );
  cover property ( $rose(out) );
  cover property ( $fell(out) );

  // Each term solely drives out high (all other terms forced false)
  // AB-only
  cover property ( (a & b) && !(c | d) && (e | f) && !g && h && !i && out );
  // CD-only
  cover property ( !(a & b) && (c | d) && (e | f) && !g && h && !i && out );
  // EF_low-only
  cover property ( !(a & b) && !(c | d) && ~(e | f) && !g && h && !i && out );
  // G-only
  cover property ( !(a & b) && !(c | d) && (e | f) && g && h && !i && out );
  // H_low-only
  cover property ( !(a & b) && !(c | d) && (e | f) && !g && !h && !i && out );
  // I-only
  cover property ( !(a & b) && !(c | d) && (e | f) && !g && h && i && out );

endmodule

// Bind into the DUT
bind multi_input_module multi_input_module_sva sva_i(.*);
// synopsys translate_on