// SVA bind file for adder: concise, checks correctness and X-prop, with focused coverage
module adder_sva (
  input logic [7:0] A, B,
  input logic [7:0] sum,
  input logic       carry_out
);

  // Check: after inputs change, outputs reflect pure 8-bit add with correct carry (next delta)
  property p_sum_ok;
    ##0 (sum === ({1'b0,A} + {1'b0,B})[7:0]);
  endproperty
  assert property (@(A or B) p_sum_ok)
    else $error("adder sum mismatch: A=%0h B=%0h sum=%0h", A, B, sum);

  property p_carry_ok;
    ##0 (carry_out === ({1'b0,A} + {1'b0,B})[8]);
  endproperty
  assert property (@(A or B) p_carry_ok)
    else $error("adder carry mismatch: A=%0h B=%0h carry_out=%0b", A, B, carry_out);

  // If inputs are known, outputs must also be known (no X/Z propagation)
  property p_knownness;
    !$isunknown({A,B}) |-> ##0 !$isunknown({sum,carry_out});
  endproperty
  assert property (@(A or B or sum or carry_out) p_knownness)
    else $error("adder outputs X/Z with known inputs: A=%0h B=%0h sum=%0h carry=%0b", A, B, sum, carry_out);

  // Targeted functional coverage (sample after outputs settle)
  cover property (@(A or B) ##0 ({1'b0,A}+{1'b0,B})[8]);                // overflow case
  cover property (@(A or B) ##0 !({1'b0,A}+{1'b0,B})[8]);               // no overflow
  cover property (@(A or B) ##0 (A==8'h00 && B==8'h00 && sum==8'h00 && !carry_out));
  cover property (@(A or B) ##0 (A==8'hFF && B==8'h01 && sum==8'h00 && carry_out)); // boundary overflow
  cover property (@(A or B) ##0 (A==8'hFF && B==8'hFF && sum==8'hFE && carry_out)); // max+max
  cover property (@(A or B or carry_out) $rose(carry_out));
  cover property (@(A or B or carry_out) $fell(carry_out));

endmodule

bind adder adder_sva sva_i (.A(A), .B(B), .sum(sum), .carry_out(carry_out));