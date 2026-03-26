module binary_latch_with_reset_sva(
    input logic CLK,
    input logic RST,
    input logic D,
    input logic Q
);

    // Reset forces Q low on the following clock sample.
    check_reset_forces_zero: assert property (
        @(posedge CLK) RST |=> (Q == 1'b0)
    );

    // A high D is captured into Q on the next clock when not in reset.
    check_capture_one: assert property (
        @(posedge CLK) disable iff (RST) D |=> (Q == 1'b1)
    );

    // A low D is captured into Q on the next clock when not in reset.
    check_capture_zero: assert property (
        @(posedge CLK) disable iff (RST) !D |=> (Q == 1'b0)
    );

endmodule