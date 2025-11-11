// SVA for modulo_operator (bind into DUT scope)
module modulo_operator_sva;
  // Sample on input changes; use ##0 to evaluate after combinational settle
  default clocking cb @(dividend or divisor); endclocking

  // Helper
  property p_known_inputs; !$isunknown({dividend,divisor}); endproperty

  // Core functional consistency (no divide-by-zero)
  assert property (p_known_inputs && (divisor != 0) |-> ##0
                   (quotient  == dividend / divisor) &&
                   (product   == quotient * divisor) &&
                   (remainder == dividend - product) &&
                   (remainder + product == dividend) &&
                   (remainder < divisor));

  // Corner cases (no divide-by-zero)
  assert property (p_known_inputs && (divisor != 0) && (divisor > dividend) |-> ##0
                   (quotient == 0) && (product == 0) && (remainder == dividend));

  assert property (p_known_inputs && (divisor == dividend) && (divisor != 0) |-> ##0
                   (quotient == 1) && (product == dividend) && (remainder == 0));

  assert property (p_known_inputs && (divisor == 1) |-> ##0
                   (quotient == dividend) && (product == dividend) && (remainder == 0));

  assert property (p_known_inputs && (dividend == 0) && (divisor != 0) |-> ##0
                   (product == 0) && (remainder == 0));

  // X-propagation / sanitization
  assert property (p_known_inputs && (divisor != 0) |-> ##0
                   !$isunknown({quotient,product,remainder}));

  assert property (p_known_inputs && (divisor == 0) |-> ##0
                   $isunknown(remainder));

  // Coverage
  cover property (p_known_inputs && (divisor == 0));                              // div-by-zero seen
  cover property (p_known_inputs && (divisor != 0) && (remainder == 0));          // exact division
  cover property (p_known_inputs && (divisor != 0) && (remainder != 0));          // non-zero remainder
  cover property (p_known_inputs && (divisor != 0) && (divisor > dividend));      // quotient=0 case
  cover property (p_known_inputs && (divisor == 1));                               // divide by 1
  cover property (p_known_inputs && (divisor != 0) && (divisor == dividend));     // divide by self
  cover property (p_known_inputs && (divisor != 0) && ((divisor & (divisor-1))==0)); // power-of-two
endmodule

bind modulo_operator modulo_operator_sva m_modulo_operator_sva();