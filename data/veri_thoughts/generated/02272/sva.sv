module simple_calculator_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic       op,
    input logic [3:0] Z
);

    // Z implements add/sub based on op (sampled on posedge of A[0]).
    check_func_on_posedge_a0: assert property (
        @(posedge A[0]) Z == ((op ? (A - B) : (A + B)) & 4'hF)
    );

    // Z implements add/sub based on op (sampled on posedge of A[1]).
    check_func_on_posedge_a1: assert property (
        @(posedge A[1]) Z == ((op ? (A - B) : (A + B)) & 4'hF)
    );

    // Z implements add/sub based on op (sampled on posedge of A[2]).
    check_func_on_posedge_a2: assert property (
        @(posedge A[2]) Z == ((op ? (A - B) : (A + B)) & 4'hF)
    );

    // Z implements add/sub based on op (sampled on posedge of B[0]).
    check_func_on_posedge_b0: assert property (
        @(posedge B[0]) Z == ((op ? (A - B) : (A + B)) & 4'hF)
    );

    // Z implements add/sub based on op (sampled on posedge of B[1]).
    check_func_on_posedge_b1: assert property (
        @(posedge B[1]) Z == ((op ? (A - B) : (A + B)) & 4'hF)
    );

    // Z implements add/sub based on op (sampled on posedge of op).
    check_func_on_posedge_op: assert property (
        @(posedge op) Z == ((op ? (A - B) : (A + B)) & 4'hF)
    );

    // When op==0 and B==0, Z equals A (sampled on posedge of A[0]).
    add_identity_b_zero: assert property (
        @(posedge A[0]) (op == 1'b0) && (B == 4'h0) |-> (Z == A)
    );

    // When op==1 and B==0, Z equals A (sampled on posedge of A[0]).
    sub_identity_b_zero: assert property (
        @(posedge A[0]) (op == 1'b1) && (B == 4'h0) |-> (Z == A)
    );

    // When op==0 and A==0, Z equals B (sampled on posedge of B[0]).
    add_identity_a_zero: assert property (
        @(posedge B[0]) (op == 1'b0) && (A == 4'h0) |-> (Z == B)
    );

    // When op==1 and A==B, Z is zero (sampled on posedge of A[0]).
    sub_equal_operands_zero: assert property (
        @(posedge A[0]) (op == 1'b1) && (A == B) |-> (Z == 4'h0)
    );

    // Addition is commutative when op==0 (sampled on posedge of A[3]).
    add_commutes: assert property (
        @(posedge A[3]) (op == 1'b0) |-> (Z == ((B + A) & 4'hF))
    );

endmodule