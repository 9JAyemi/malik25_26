module and_xnor_inv_sva (
    input logic a,
    input logic b,
    input logic g_out,
    input logic p_out
);
    // No clock or reset in RTL; pure combinational; sample on posedge of a or b.

    // g_out implements a AND b.
    check_and_definition: assert property (
        @(posedge a or posedge b) g_out == (a & b)
    );

    // p_out implements a XOR b (since XNOR(~a,b) == a^b).
    check_xor_definition: assert property (
        @(posedge a or posedge b) p_out == (a ^ b)
    );

    // g_out and p_out are never both HIGH.
    check_outputs_mutex: assert property (
        @(posedge a or posedge b) !(g_out & p_out)
    );

    // OR of outputs equals OR of inputs.
    check_or_identity: assert property (
        @(posedge a or posedge b) (g_out | p_out) == (a | b)
    );

    // XOR of outputs equals OR of inputs (disjoint sum).
    check_xor_or_identity: assert property (
        @(posedge a or posedge b) (g_out ^ p_out) == (a | b)
    );

    // Truth table: a=0, b=0 -> g_out=0, p_out=0.
    check_case_00: assert property (
        @(posedge a or posedge b) (!a && !b) |-> (!g_out && !p_out)
    );

    // Truth table: a=0, b=1 -> g_out=0, p_out=1.
    check_case_01: assert property (
        @(posedge a or posedge b) (!a && b) |-> (!g_out && p_out)
    );

    // Truth table: a=1, b=0 -> g_out=0, p_out=1.
    check_case_10: assert property (
        @(posedge a or posedge b) (a && !b) |-> (!g_out && p_out)
    );

    // Truth table: a=1, b=1 -> g_out=1, p_out=0.
    check_case_11: assert property (
        @(posedge a or posedge b) (a && b) |-> (g_out && !p_out)
    );
endmodule