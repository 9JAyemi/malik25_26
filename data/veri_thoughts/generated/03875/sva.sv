module dff_sva (
    input logic D,
    input logic RST,
    input logic SET,
    input logic CLK,
    input logic Q
);

    // Clock: CLK; reset: RST is active-high and synchronous.
    // Function: sequential DFF with reset priority, then set, then D capture.

    // When reset is asserted on a rising clock edge, Q clears low.
    check_reset_clears_q: assert property (
        @(posedge CLK) RST |=> (Q == 1'b0)
    );

    // When SET is asserted without reset, Q is driven high.
    check_set_sets_q: assert property (
        @(posedge CLK) disable iff (RST) SET |=> (Q == 1'b1)
    );

    // With no control active and D high, Q captures a 1.
    check_data_high_captures_q: assert property (
        @(posedge CLK) disable iff (RST) (!SET && D) |=> (Q == 1'b1)
    );

    // With no control active and D low, Q captures a 0.
    check_data_low_captures_q: assert property (
        @(posedge CLK) disable iff (RST) (!SET && !D) |=> (Q == 1'b0)
    );

endmodule