module and_module_sva (
    input logic a,
    input logic b,
    input logic c,
    input logic d,
    input logic out0,
    input logic out1,
    input logic out2,
    input logic out3
);

    // out0 is the AND of a and b.
    check_out0_is_and_ab: assert property (
        @($global_clock) out0 == (a & b)
    );

    // out1 is the AND of b and c.
    check_out1_is_and_bc: assert property (
        @($global_clock) out1 == (b & c)
    );

    // out2 follows the conditional assignment from a and d.
    check_out2_is_conditional_ad: assert property (
        @($global_clock) out2 == ((a == 1'b1) ? d : 1'b0)
    );

    // out3 is the AND of b and d.
    check_out3_is_and_bd: assert property (
        @($global_clock) out3 == (b & d)
    );

endmodule