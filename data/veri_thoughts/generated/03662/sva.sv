module TLATCH_sva (
    input logic E,
    input logic SE,
    input logic CK,
    input logic D,
    input logic ECK
);

    // When E is low, the output must be low.
    check_output_low_when_e_low: assert property (
        @(posedge CK) !E |-> !ECK
    );

    // A sampled low E clears the stored state by the next clock sample.
    check_clear_visible_next_clock: assert property (
        @(posedge CK) !E |=> !ECK
    );

    // Sampling D=0 with SE high forces the next sampled output low.
    check_capture_zero_drives_low: assert property (
        @(posedge CK) disable iff (!E) (SE && !D) |=> !ECK
    );

    // In hold mode, a sampled low output stays low on the next clock sample.
    check_hold_preserves_low: assert property (
        @(posedge CK) disable iff (!E) (!SE && !ECK) |=> !ECK
    );

    // A sampled low-to-high output transition requires SE high at the prior sample.
    check_rise_requires_sample_enable: assert property (
        @(posedge CK) disable iff (!E) (!ECK ##1 ECK) |-> SE
    );

    // A sampled low-to-high output transition requires D high at the prior sample.
    check_rise_requires_data_one: assert property (
        @(posedge CK) disable iff (!E) (!ECK ##1 ECK) |-> D
    );

endmodule