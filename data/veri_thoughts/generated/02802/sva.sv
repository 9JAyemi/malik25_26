module StepDecoder_sva (
    input logic clk,
    input logic reset_n,
    input logic [15:0] TimeSteps,
    input logic [3:0] StepCounter
);
    // DUT is pure combinational; clk/reset_n are for SVA sampling only.

    // Exactly one TimeSteps bit is HIGH (one-hot decode).
    check_onehot_timesteps: assert property (
        @(posedge clk) disable iff (!reset_n) $onehot(TimeSteps)
    );

    // TimeSteps[0] matches ~3 & ~2 & ~1 & ~0.
    check_ts0_decode: assert property (
        @(posedge clk) disable iff (!reset_n)
            (TimeSteps[0] == (~StepCounter[3] & ~StepCounter[2] & ~StepCounter[1] & ~StepCounter[0]))
    );
    // TimeSteps[1] matches ~3 & ~2 & ~1 & 0.
    check_ts1_decode: assert property (
        @(posedge clk) disable iff (!reset_n)
            (TimeSteps[1] == (~StepCounter[3] & ~StepCounter[2] & ~StepCounter[1] & StepCounter[0]))
    );
    // TimeSteps[2] matches ~3 & ~2 & 1 & ~0.
    check_ts2_decode: assert property (
        @(posedge clk) disable iff (!reset_n)
            (TimeSteps[2] == (~StepCounter[3] & ~StepCounter[2] & StepCounter[1] & ~StepCounter[0]))
    );
    // TimeSteps[3] matches ~3 & ~2 & 1 & 0.
    check_ts3_decode: assert property (
        @(posedge clk) disable iff (!reset_n)
            (TimeSteps[3] == (~StepCounter[3] & ~StepCounter[2] & StepCounter[1] & StepCounter[0]))
    );
    // TimeSteps[4] matches ~3 & 2 & ~1 & ~0.
    check_ts4_decode: assert property (
        @(posedge clk) disable iff (!reset_n)
            (TimeSteps[4] == (~StepCounter[3] & StepCounter[2] & ~StepCounter[1] & ~StepCounter[0]))
    );
    // TimeSteps[5] matches ~3 & 2 & ~1 & 0.
    check_ts5_decode: assert property (
        @(posedge clk) disable iff (!reset_n)
            (TimeSteps[5] == (~StepCounter[3] & StepCounter[2] & ~StepCounter[1] & StepCounter[0]))
    );
    // TimeSteps[6] matches ~3 & 2 & 1 & ~0.
    check_ts6_decode: assert property (
        @(posedge clk) disable iff (!reset_n)
            (TimeSteps[6] == (~StepCounter[3] & StepCounter[2] & StepCounter[1] & ~StepCounter[0]))
    );
    // TimeSteps[7] matches ~3 & 2 & 1 & 0.
    check_ts7_decode: assert property (
        @(posedge clk) disable iff (!reset_n)
            (TimeSteps[7] == (~StepCounter[3] & StepCounter[2] & StepCounter[1] & StepCounter[0]))
    );
    // TimeSteps[8] matches 3 & ~2 & ~1 & ~0.
    check_ts8_decode: assert property (
        @(posedge clk) disable iff (!reset_n)
            (TimeSteps[8] == (StepCounter[3] & ~StepCounter[2] & ~StepCounter[1] & ~StepCounter[0]))
    );
    // TimeSteps[9] matches 3 & ~2 & ~1 & 0.
    check_ts9_decode: assert property (
        @(posedge clk) disable iff (!reset_n)
            (TimeSteps[9] == (StepCounter[3] & ~StepCounter[2] & ~StepCounter[1] & StepCounter[0]))
    );
    // TimeSteps[10] matches 3 & ~2 & 1 & ~0.
    check_ts10_decode: assert property (
        @(posedge clk) disable iff (!reset_n)
            (TimeSteps[10] == (StepCounter[3] & ~StepCounter[2] & StepCounter[1] & ~StepCounter[0]))
    );
    // TimeSteps[11] matches 3 & ~2 & 1 & 0.
    check_ts11_decode: assert property (
        @(posedge clk) disable iff (!reset_n)
            (TimeSteps[11] == (StepCounter[3] & ~StepCounter[2] & StepCounter[1] & StepCounter[0]))
    );
    // TimeSteps[12] matches 3 & 2 & ~1 & ~0.
    check_ts12_decode: assert property (
        @(posedge clk) disable iff (!reset_n)
            (TimeSteps[12] == (StepCounter[3] & StepCounter[2] & ~StepCounter[1] & ~StepCounter[0]))
    );
    // TimeSteps[13] matches 3 & 2 & ~1 & 0.
    check_ts13_decode: assert property (
        @(posedge clk) disable iff (!reset_n)
            (TimeSteps[13] == (StepCounter[3] & StepCounter[2] & ~StepCounter[1] & StepCounter[0]))
    );
    // TimeSteps[14] matches 3 & 2 & 1 & ~0.
    check_ts14_decode: assert property (
        @(posedge clk) disable iff (!reset_n)
            (TimeSteps[14] == (StepCounter[3] & StepCounter[2] & StepCounter[1] & ~StepCounter[0]))
    );
    // TimeSteps[15] matches 3 & 2 & 1 & 0.
    check_ts15_decode: assert property (
        @(posedge clk) disable iff (!reset_n)
            (TimeSteps[15] == (StepCounter[3] & StepCounter[2] & StepCounter[1] & StepCounter[0]))
    );

endmodule