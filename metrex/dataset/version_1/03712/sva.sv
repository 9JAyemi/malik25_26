// SVA checker for LUT. Bind this to the DUT.
module LUT_sva #(parameter SIZE=8)
(
  input  logic [SIZE-1:0]   A,
  input  logic [1:0]        B,
  input  logic [SIZE+1:0]   Result
);

  // Helper: spec-computed expected result
  function automatic logic [SIZE+1:0] expected(input logic [SIZE-1:0] a, input logic [1:0] b);
    case (b)
      2'b00: expected = '0;
      2'b01: expected = {{2{1'b0}}, a};
      2'b10: expected = {1'b0, a, 1'b0};
      2'b11: expected = {2'b0, a, 2'b0};
      default: expected = 'x;
    endcase
  endfunction

  // Main functional check (no latency; allow NBA settle with ##0)
  a_func: assert property (@(A or B)
    !$isunknown({A,B}) |-> ##0 (Result === expected(A,B))
  ) else $error("LUT: Result mismatch. A=%0h B=%0b Result=%0h exp=%0h", A, B, Result, expected(A,B));

  // Output must be known whenever inputs are known
  a_no_x: assert property (@(A or B)
    !$isunknown({A,B}) |-> ##0 !$isunknown(Result)
  ) else $error("LUT: Result has X/Z with known inputs. A=%0h B=%0b Result=%0h", A, B, Result);

  // Bit-accurate per-select checks (explicit mapping)
  a_b00: assert property (@(A or B)
    (!$isunknown({A,B}) && B==2'b00) |-> ##0 (Result == '0)
  );

  a_b01: assert property (@(A or B)
    (!$isunknown({A,B}) && B==2'b01) |-> ##0 (Result[SIZE+1:SIZE]==2'b00 && Result[SIZE-1:0]==A)
  );

  a_b10: assert property (@(A or B)
    (!$isunknown({A,B}) && B==2'b10) |-> ##0 (Result[SIZE+1]==1'b0 && Result[0]==1'b0 && Result[SIZE:1]==A)
  );

  a_b11: assert property (@(A or B)
    (!$isunknown({A,B}) && B==2'b11) |-> ##0 (Result[SIZE+1:SIZE]==2'b00 && Result[1:0]==2'b00 && Result[SIZE-1:2]==A)
  );

  // Functional coverage
  c_b00: cover property (@(A or B) (!$isunknown({A,B})) ##0 (B==2'b00 && Result=='0));
  c_b01: cover property (@(A or B) (!$isunknown({A,B})) ##0 (B==2'b01 && Result[SIZE-1:0]==A));
  c_b10: cover property (@(A or B) (!$isunknown({A,B})) ##0 (B==2'b10 && Result[SIZE:1]==A && Result[0]==0));
  c_b11: cover property (@(A or B) (!$isunknown({A,B})) ##0 (B==2'b11 && Result[SIZE-1:2]==A && Result[1:0]==0));

  // Corner patterns
  c_A_zero:     cover property (@(A or B) (!$isunknown({A,B})) ##0 (A=='0));
  c_A_all_ones: cover property (@(A or B) (!$isunknown({A,B})) ##0 (A=={SIZE{1'b1}}));

endmodule

// Bind into DUT
bind LUT LUT_sva #(.SIZE(SIZE)) u_LUT_sva (.A(A), .B(B), .Result(Result));