module TLATNTSCAX2TS_sva (
    input logic E,
    input logic SE,
    input logic CK,
    input logic ECK
);

// ECK must match the RTL combinational equation.
    check_function_equivalence: assert property (
        @(posedge CK) ECK == ((E & SE) | (!E & CK))
    );

// When E is low, ECK must follow CK.
    check_eck_follows_ck_when_e_low: assert property (
        @(posedge CK) !E |-> (ECK == CK)
    );

// When E is high, ECK must follow SE.
    check_eck_follows_se_when_e_high: assert property (
        @(posedge CK) E |-> (ECK == SE)
    );

// A high SE with low E must drive ECK high.
    check_se_high_drives_eck_high_when_e_low: assert property (
        @(posedge CK) (SE && !E) |-> (ECK == 1'b1)
    );

// A low SE with low E must drive ECK low.
    check_se_low_drives_eck_low_when_e_low: assert property (
        @(posedge CK) (!SE && !E) |-> (ECK == 1'b0)
    );

// A high E with low SE must drive ECK low.
    check_e_high_se_low_drives_eck_low: assert property (
        @(posedge CK) (E && !SE) |-> (ECK == 1'b0)
    );

// A high E with high SE must drive ECK high.
    check_e_high_se_high_drives_eck_high: assert property (
        @(posedge CK) (E && SE) |-> (ECK == 1'b1)
    );

endmodule
