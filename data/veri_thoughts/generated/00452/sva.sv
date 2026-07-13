module TLATNTSCAX2TS_sva (
    input logic E,
    input logic SE,
    input logic CK,
    input logic ECK
);

    // During CK low, the gated output must be low.
    check_eck_low_during_ck_low: assert property (
        @(posedge CK) ECK == 1'b0
    );

    // During CK high, the gated output must match E & SE.
    check_eck_matches_enables_during_ck_high: assert property (
        @(negedge CK) ECK == (E & SE)
    );

endmodule