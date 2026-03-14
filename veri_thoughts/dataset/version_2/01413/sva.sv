module logic_operations_sva (
    input logic CLK,
    input logic RESETn,
    input logic a,
    input logic b,
    input logic g_out,
    input logic p_out
);
    // p_out equals XOR of a and b.
    check_pout_xor: assert property (
        @(posedge CLK) disable iff (!RESETn) p_out == (a ^ b)
    );

    // g_out equals AND of a and b.
    check_gout_and: assert property (
        @(posedge CLK) disable iff (!RESETn) g_out == (a & b)
    );

    // When both inputs are 1, g_out=1 and p_out=0.
    check_tt_11: assert property (
        @(posedge CLK) disable iff (!RESETn) (a && b) |-> (g_out && !p_out)
    );

    // When both inputs are 0, both outputs are 0.
    check_tt_00: assert property (
        @(posedge CLK) disable iff (!RESETn) (!a && !b) |-> (!g_out && !p_out)
    );

    // When inputs differ, p_out=1 and g_out=0.
    check_tt_10_01: assert property (
        @(posedge CLK) disable iff (!RESETn) (a ^ b) |-> (p_out && !g_out)
    );

    // g_out high implies p_out low (cannot both be 1).
    check_gout_implies_not_pout: assert property (
        @(posedge CLK) disable iff (!RESETn) g_out |-> !p_out
    );

    // p_out high implies inputs differ.
    check_pout_implies_inputs_differ: assert property (
        @(posedge CLK) disable iff (!RESETn) p_out |-> (a ^ b)
    );

    // Both outputs low implies both inputs low.
    check_both_outputs_zero_implies_inputs_zero: assert property (
        @(posedge CLK) disable iff (!RESETn) (!p_out && !g_out) |-> (!a && !b)
    );

    // If either input is 0, g_out must be 0.
    check_input_zero_forces_gout_zero: assert property (
        @(posedge CLK) disable iff (!RESETn) ((!a) || (!b)) |-> (g_out == 1'b0)
    );

    // OR of outputs equals OR of inputs.
    check_outputs_cover_or: assert property (
        @(posedge CLK) disable iff (!RESETn) ((p_out | g_out) == (a | b))
    );
endmodule