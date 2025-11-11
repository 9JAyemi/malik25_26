// SVA for adder
module adder_sva(
    input logic [7:0] A,
    input logic [7:0] B,
    input logic [8:0] sum
);

    // Functional correctness (sample sum after delta to avoid race with continuous assign)
    assert property (@(A or B) !$isunknown({A,B}) |-> ##0 sum == ({1'b0,A} + {1'b0,B}))
      else $error("adder: sum mismatch A=%0h B=%0h sum=%0h", A, B, sum);

    // Decomposed checks
    assert property (@(A or B) !$isunknown({A,B}) |-> ##0 sum[7:0] == (A + B))
      else $error("adder: low byte mismatch A=%0h B=%0h sum=%0h", A, B, sum);
    assert property (@(A or B) !$isunknown({A,B}) |-> ##0 sum[8] == ({1'b0,A}+{1'b0,B})[8])
      else $error("adder: carry mismatch A=%0h B=%0h sum=%0h", A, B, sum);

    // No X/Z on output when inputs are known
    assert property (@(A or B) !$isunknown({A,B}) |-> ##0 !$isunknown(sum))
      else $error("adder: X/Z on sum with known inputs A=%0h B=%0h sum=%0h", A, B, sum);

    // Targeted functional coverage
    cover property (@(A or B) (A==8'h00 && B==8'h00) ##0 (sum==9'h000));
    cover property (@(A or B) (A==8'hFF && B==8'h00) ##0 (sum==9'h0FF));
    cover property (@(A or B) (A==8'h00 && B==8'hFF) ##0 (sum==9'h0FF));
    cover property (@(A or B) (A==8'hFF && B==8'hFF) ##0 (sum==9'h1FE)); // overflow max
    cover property (@(A or B) (A==8'h80 && B==8'h80) ##0 (sum==9'h100)); // mid overflow
    cover property (@(A or B) !$isunknown({A,B}) ##0 (sum[8]==1'b0));    // no carry
    cover property (@(A or B) !$isunknown({A,B}) ##0 (sum[8]==1'b1));    // carry
endmodule

// Bind into DUT
bind adder adder_sva u_adder_sva (.A(A), .B(B), .sum(sum));