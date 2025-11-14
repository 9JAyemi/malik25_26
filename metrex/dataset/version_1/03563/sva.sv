// SVA for adder: concise, high-quality checks and coverage
module adder_sva #(parameter WIDTH = 8)
(
  input  logic [WIDTH-1:0] A,
  input  logic [WIDTH-1:0] B,
  input  logic [WIDTH-1:0] sum
);

  function automatic logic [WIDTH-1:0] low_sum(input logic [WIDTH-1:0] a, b);
    low_sum = a + b; // wraps naturally to WIDTH
  endfunction

  function automatic logic carry_bit(input logic [WIDTH-1:0] a, b);
    carry_bit = ({1'b0,a} + {1'b0,b})[WIDTH];
  endfunction

  // Correctness: sum always equals A+B (wrapped to WIDTH)
  assert property (@(A or B or sum) sum == low_sum(A,B))
    else $error("adder: sum != A+B (A=%0h B=%0h sum=%0h)", A, B, sum);

  // Output only changes when inputs change
  assert property (@(sum) 1 |-> ($changed(A) || $changed(B)))
    else $error("adder: sum changed without input change (A=%0h B=%0h sum=%0h)", A, B, sum);

  // Known inputs imply known output (no X/Z propagation)
  assert property (@(A or B or sum) !$isunknown({A,B}) |-> !$isunknown(sum))
    else $error("adder: X/Z on sum with known inputs (A=%0h B=%0h sum=%0h)", A, B, sum);

  // While inputs are stable, output must remain stable
  assert property (@(A or B or sum) $stable({A,B}) |-> $stable(sum))
    else $error("adder: sum changed while inputs stable (A=%0h B=%0h sum=%0h)", A, B, sum);

  // Functional coverage
  cover property (@(A or B) carry_bit(A,B));                         // overflow/wrap
  cover property (@(A or B) !carry_bit(A,B));                        // no overflow
  cover property (@(A or B) (A==0 && B==0) && (sum==0));             // 0+0->0
  cover property (@(A or B) (A==0 && sum==B));                       // identity A=0
  cover property (@(A or B) (B==0 && sum==A));                       // identity B=0
  cover property (@(A or B) (A==8'hFF && B==8'h01) && (sum==8'h00)); // classic wrap
  cover property (@(A or B) (A==B));                                 // equal operands
  cover property (@(A or B) (sum==0) && (|{A,B}));                   // nonzero wrap to zero

endmodule

bind adder adder_sva #(.WIDTH(8)) adder_sva_i (.A(A), .B(B), .sum(sum));