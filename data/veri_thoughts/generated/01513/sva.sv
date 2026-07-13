module top_module_sva (
    input logic a,
    input logic b,
    input logic c,
    input logic out
);
    ///// Combinational function correctness /////
    // Out equals NAND(a,b) OR (NAND(a,b) XOR c).
    check_func_via_gate_chain: assert property (
        @(posedge a) out == ((~(a & b)) | ((~(a & b)) ^ c))
    );
    // Out equals (~a) | (~b) | c (simplified form).
    check_func_demorgan: assert property (
        @(posedge a) out == ((~a) | (~b) | c)
    );

    ///// Canonical input/output implications /////
    // If a is LOW then out is HIGH.
    check_out_high_when_a_low: assert property (
        @(posedge b) (!a) |-> (out == 1'b1)
    );
    // If b is LOW then out is HIGH.
    check_out_high_when_b_low: assert property (
        @(posedge a) (!b) |-> (out == 1'b1)
    );
    // If c is HIGH then out is HIGH.
    check_out_high_when_c_high: assert property (
        @(posedge a) (c) |-> (out == 1'b1)
    );

    ///// Corner cases and equivalences /////
    // Out is zero only when a=1,b=1,c=0.
    check_only_zero_on_110: assert property (
        @(posedge a) (out == 1'b0) |-> (a && b && !c)
    );
    // When a=1 and b=1, out equals c.
    check_ab_high_out_equals_c: assert property (
        @(posedge a) (a && b) |-> (out == c)
    );
    // When c=0, out equals ~(a & b).
    check_c_low_out_equals_nand: assert property (
        @(posedge a) (!c) |-> (out == ~(a & b))
    );
    // When a=1 and c=0, out equals ~b.
    check_a_high_c_low_out_equals_notb: assert property (
        @(posedge a) (a && !c) |-> (out == ~b)
    );
    // When b=1 and c=0, out equals ~a.
    check_b_high_c_low_out_equals_nota: assert property (
        @(posedge a) (b && !c) |-> (out == ~a)
    );
    // If a=1,b=1,c=0 then out is 0 (explicit zero-case).
    check_110_implies_zero: assert property (
        @(posedge a) (a && b && !c) |-> (out == 1'b0)
    );
endmodule