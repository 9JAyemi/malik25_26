// SVA for adder: concise, high-quality checks and coverage.
// Bindable assertion module (no clock required; samples on input changes).

module adder_sva (
  input  logic [7:0] A,
  input  logic [7:0] B,
  input  logic [7:0] sum,
  input  logic       carry_out
);

  // Deterministic behavior and no-X outputs when inputs are known
  always @* begin
    if (!$isunknown({A,B})) begin
      assert ({carry_out, sum} == ({1'b0, A} + {1'b0, B}))
        else $error("adder mismatch: A=%0h B=%0h sum=%0h carry=%0b", A, B, sum, carry_out);
      assert (!$isunknown({sum,carry_out}))
        else $error("adder X/Z outputs with known inputs: A=%0h B=%0h", A, B);
    end
  end

  // Identities for zero operands
  property p_zeroB;
    @(A or B) !$isunknown({A,B}) && (B==8'h00) |-> (sum==A && carry_out==1'b0);
  endproperty
  assert property (p_zeroB);

  property p_zeroA;
    @(A or B) !$isunknown({A,B}) && (A==8'h00) |-> (sum==B && carry_out==1'b0);
  endproperty
  assert property (p_zeroA);

  // Carry flag equivalence (redundant to main check but explicit)
  property p_carry_flag;
    @(A or B) !$isunknown({A,B}) |-> (carry_out == (({1'b0,A}+{1'b0,B})[8]));
  endproperty
  assert property (p_carry_flag);

  // Functional coverage (key corners and carry/no-carry)
  cover property (@(A or B) !$isunknown({A,B}) && carry_out==1'b0);
  cover property (@(A or B) !$isunknown({A,B}) && carry_out==1'b1);
  cover property (@(A or B) !$isunknown({A,B}) && A==8'h00 && B==8'h00);
  cover property (@(A or B) !$isunknown({A,B}) && A==8'hFF && B==8'h01); // wrap to 0
  cover property (@(A or B) !$isunknown({A,B}) && A==8'h7F && B==8'h80); // 0xFF no carry
  cover property (@(A or B) !$isunknown({A,B}) && A==8'hFF && B==8'hFF); // max+max
  cover property (@(A or B) !$isunknown({A,B}) && sum==8'h00 && carry_out==1'b1);

endmodule

bind adder adder_sva adder_sva_i (.*);