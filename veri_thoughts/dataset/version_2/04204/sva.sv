module dff_with_set_sva (
    input logic D,
    input logic SET,
    input logic CLK,
    input logic Q
);

    // SET synchronously forces Q high.
    check_sync_set_forces_q_high: assert property (
        @(posedge CLK) SET |=> (Q == 1'b1)
    );

    // When SET is low, a high D is captured into Q.
    check_capture_d_high_when_set_low: assert property (
        @(posedge CLK) (!SET && D) |=> (Q == 1'b1)
    );

    // When SET is low, a low D is captured into Q.
    check_capture_d_low_when_set_low: assert property (
        @(posedge CLK) (!SET && !D) |=> (Q == 1'b0)
    );

endmodule