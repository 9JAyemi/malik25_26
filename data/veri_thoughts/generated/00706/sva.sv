module sky130_fd_sc_lp__ha_sva (
    input logic COUT,
    input logic SUM,
    input logic A,
    input logic B
);
    // COUT equals logical AND of A and B.
    check_cout_definition: assert property (
        @(posedge $global_clock) COUT == (A & B)
    );

    // SUM equals logical XOR of A and B.
    check_sum_definition: assert property (
        @(posedge $global_clock) SUM == (A ^ B)
    );

    // When A=0 and B=0 then SUM=0 and COUT=0.
    check_tt_00: assert property (
        @(posedge $global_clock) (A==1'b0 && B==1'b0) |-> (SUM==1'b0 && COUT==1'b0)
    );

    // When A=0 and B=1 then SUM=1 and COUT=0.
    check_tt_01: assert property (
        @(posedge $global_clock) (A==1'b0 && B==1'b1) |-> (SUM==1'b1 && COUT==1'b0)
    );

    // When A=1 and B=0 then SUM=1 and COUT=0.
    check_tt_10: assert property (
        @(posedge $global_clock) (A==1'b1 && B==1'b0) |-> (SUM==1'b1 && COUT==1'b0)
    );

    // When A=1 and B=1 then SUM=0 and COUT=1.
    check_tt_11: assert property (
        @(posedge $global_clock) (A==1'b1 && B==1'b1) |-> (SUM==1'b0 && COUT==1'b1)
    );

    // SUM and COUT are never both HIGH.
    check_outputs_not_both_high: assert property (
        @(posedge $global_clock) !(SUM && COUT)
    );

    // SUM=1 implies inputs differ.
    check_sum_high_inputs_differ: assert property (
        @(posedge $global_clock) SUM |-> (A != B)
    );

    // COUT=1 implies both inputs are 1.
    check_cout_high_inputs_one: assert property (
        @(posedge $global_clock) COUT |-> (A && B)
    );

    // Inputs equal implies SUM=0.
    check_inputs_equal_sum_low: assert property (
        @(posedge $global_clock) (A == B) |-> (SUM == 1'b0)
    );
endmodule