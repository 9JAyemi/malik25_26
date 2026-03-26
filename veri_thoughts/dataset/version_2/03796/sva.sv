module majority_logic_sva (
    input logic a,
    input logic b,
    input logic c,
    input logic out
);

    // 111 drives out high.
    check_out_high_for_111: assert property (
        @($global_clock) ({a,b,c} == 3'b111) |-> (out == 1'b1)
    );

    // 110 drives out high.
    check_out_high_for_110: assert property (
        @($global_clock) ({a,b,c} == 3'b110) |-> (out == 1'b1)
    );

    // 101 drives out high.
    check_out_high_for_101: assert property (
        @($global_clock) ({a,b,c} == 3'b101) |-> (out == 1'b1)
    );

    // 011 drives out high.
    check_out_high_for_011: assert property (
        @($global_clock) ({a,b,c} == 3'b011) |-> (out == 1'b1)
    );

    // 100 drives out low.
    check_out_low_for_100: assert property (
        @($global_clock) ({a,b,c} == 3'b100) |-> (out == 1'b0)
    );

    // 010 drives out low.
    check_out_low_for_010: assert property (
        @($global_clock) ({a,b,c} == 3'b010) |-> (out == 1'b0)
    );

    // 001 drives out low.
    check_out_low_for_001: assert property (
        @($global_clock) ({a,b,c} == 3'b001) |-> (out == 1'b0)
    );

    // 000 drives out low.
    check_out_low_for_000: assert property (
        @($global_clock) ({a,b,c} == 3'b000) |-> (out == 1'b0)
    );

endmodule