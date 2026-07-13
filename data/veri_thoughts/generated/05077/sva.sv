module XOR_GATE_assertions (
    input logic IN1,
    input logic OUT1
);

    // OUT1 must always implement IN1 xor 1'b1.
    check_out1_matches_xor: assert property (
        @($global_clock) OUT1 === (IN1 ^ 1'b1)
    );

    // A low IN1 must drive OUT1 high.
    check_out1_high_when_in1_low: assert property (
        @($global_clock) (IN1 === 1'b0) |-> (OUT1 === 1'b1)
    );

    // A high IN1 must drive OUT1 low.
    check_out1_low_when_in1_high: assert property (
        @($global_clock) (IN1 === 1'b1) |-> (OUT1 === 1'b0)
    );

endmodule