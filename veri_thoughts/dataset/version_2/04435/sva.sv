module d_ff_set_clr_sva (
    input logic CLK,
    input logic D,
    input logic SET,
    input logic CLR,
    input logic Q
);

    // When SET and CLR are both high, SET has priority and Q becomes 1.
    check_set_priority_over_clear: assert property (
        @(posedge CLK) (SET && CLR) |=> (Q == 1'b1)
    );

    // When only SET is high, Q becomes 1.
    check_set_drives_q_high: assert property (
        @(posedge CLK) (SET && !CLR) |=> (Q == 1'b1)
    );

    // When SET is low and CLR is high, Q becomes 0.
    check_clear_drives_q_low: assert property (
        @(posedge CLK) (!SET && CLR) |=> (Q == 1'b0)
    );

    // When SET and CLR are low, D=1 is captured into Q.
    check_capture_data_one: assert property (
        @(posedge CLK) (!SET && !CLR && D) |=> (Q == 1'b1)
    );

    // When SET and CLR are low, D=0 is captured into Q.
    check_capture_data_zero: assert property (
        @(posedge CLK) (!SET && !CLR && !D) |=> (Q == 1'b0)
    );

endmodule