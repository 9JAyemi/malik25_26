// SVA checker for output_generator
// Bind this module to the DUT:  bind output_generator output_generator_sva sva (.*);

module output_generator_sva(
  input  [3:0] num1,
  input  [3:0] num2,
  input  [1:0] operation,
  input  [3:0] result
);

  // Functional correctness (mask to 4 bits to match DUT truncation)
  assert property ( (!$isunknown({num1,num2,operation})) && (operation==2'b00)
                  |-> result == ((num1 + num2) & 4'hF) )
    else $error("ADD mismatch");

  assert property ( (!$isunknown({num1,num2,operation})) && (operation==2'b01)
                  |-> result == ((num1 - num2) & 4'hF) )
    else $error("SUB mismatch");

  assert property ( (!$isunknown({num1,num2,operation})) && (operation==2'b10)
                  |-> result == ((num1 * num2) & 4'hF) )
    else $error("MUL mismatch");

  assert property ( (!$isunknown({num1,num2,operation})) && (operation==2'b11) && (num2!=0)
                  |-> result == ((num1 / num2) & 4'hF) )
    else $error("DIV mismatch (non-zero)");

  // Division-by-zero is illegal; flag it
  assert property ( !((operation==2'b11) && (num2==0)) )
    else $error("Illegal divide-by-zero");

  // Default branch behavior when operation is unknown
  assert property ( $isunknown(operation) |-> result == 4'b0000 )
    else $error("Default case behavior violated for unknown operation");

  // Result must be known for legal, fully-known inputs
  assert property ( (!$isunknown({num1,num2,operation})) && !((operation==2'b11)&&(num2==0))
                  |-> !$isunknown(result) )
    else $error("Result X/Z with legal, known inputs");

  // Lightweight covers for op and key corner cases
  cover property ( (operation==2'b00) );                                // add seen
  cover property ( (operation==2'b01) );                                // sub seen
  cover property ( (operation==2'b10) );                                // mul seen
  cover property ( (operation==2'b11) && (num2!=0) );                   // div seen
  cover property ( (operation==2'b00) && ((num1 + num2) >  4'hF) );     // add overflow
  cover property ( (operation==2'b01) && (num1 < num2) );               // sub underflow
  cover property ( (operation==2'b10) && ((num1 * num2) >  4'hF) );     // mul overflow
  cover property ( (operation==2'b11) && (num2==0) );                   // div-by-zero stimulus
  cover property ( (operation==2'b11) && (num2!=0) && ((num1 % num2)!=0) ); // div remainder

endmodule