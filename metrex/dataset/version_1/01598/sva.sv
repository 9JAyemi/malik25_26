// SVA for multiplier_2x2
// Concise, high-quality checks and functional coverage.
// Bind this module to the DUT.

module multiplier_2x2_sva (
    input  logic [1:0] A,
    input  logic [1:0] B,
    input  logic [3:0] P,
    input  logic [3:0] Q
);
  // React on any relevant activity; use ##0 to avoid delta races and allow settle
  default clocking cb @ (A or B or P or Q); endclocking

  // Functional correctness (partial products, zero-extended to 4b)
  property p_partial_products_ok;
    disable iff ($isunknown({A,B}))
      1'b1 |-> ##0 ( P == {2'b00, (B[0] ? A : 2'b00)}
                  && Q == {2'b00, (B[1] ? A : 2'b00)} );
  endproperty
  a_partial_products_ok: assert property (p_partial_products_ok)
    else $error("P/Q mismatch: A=%0d B=%0d P=%0d Q=%0d", A, B, P, Q);

  // Known-propagation: known inputs imply known outputs (after settle)
  a_known_propagation: assert property (
    (!$isunknown({A,B})) |-> ##0 (!$isunknown({P,Q}))
  ) else $error("Unknown X/Z on outputs with known inputs");

  // Optional explicit zero-extend checks (redundant with p_partial_products_ok but very clear)
  a_zero_ext_P: assert property (##0 P[3:2] == 2'b00)
    else $error("P[3:2] must be 0");
  a_zero_ext_Q: assert property (##0 Q[3:2] == 2'b00)
    else $error("Q[3:2] must be 0");

  // Functional coverage: all 16 input combinations produce expected outputs
  genvar i, j;
  generate
    for (i = 0; i < 4; i++) begin : gen_A
      for (j = 0; j < 4; j++) begin : gen_B
        localparam logic [1:0] I = i[1:0];
        localparam logic [1:0] J = j[1:0];
        localparam logic [3:0] EXP_P = {2'b00, (J[0] ? I : 2'b00)};
        localparam logic [3:0] EXP_Q = {2'b00, (J[1] ? I : 2'b00)};
        c_ab_map_ok: cover property ( (A==I && B==J) ##0 (P==EXP_P && Q==EXP_Q) );
      end
    end
  endgenerate

  // Toggle coverage: each control bit of B independently gates A into P/Q at least once
  c_gate_b0: cover property ( (!$isunknown(A) && A!=2'b00 && B[0]==0) ##1 (B[0]==1) ##0 (P=={2'b00,A}) );
  c_gate_b1: cover property ( (!$isunknown(A) && A!=2'b00 && B[1]==0) ##1 (B[1]==1) ##0 (Q=={2'b00,A}) );

endmodule

// Bind to DUT
bind multiplier_2x2 multiplier_2x2_sva sva (.*);