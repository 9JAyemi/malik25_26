module binary_counter_sva #(
    parameter int unsigned MAX_VALUE = 16
) (
    input logic CLK,
    input logic CLR_B,
    input logic LOAD,
    input logic [4:0] DATA_IN,
    input logic [4:0] Q
);

    // CLR_B clears Q on the next clock.
    check_clear_sets_zero: assert property (
        @(posedge CLK) CLR_B |=> (Q == 5'd0)
    );

    // LOAD captures DATA_IN when CLR_B is low.
    check_load_captures_data: assert property (
        @(posedge CLK) disable iff (CLR_B) LOAD |=> (Q == $past(DATA_IN))
    );

    // LOAD has priority over the terminal-count wrap behavior.
    check_load_priority_over_wrap: assert property (
        @(posedge CLK) disable iff (CLR_B) (LOAD && (Q == (MAX_VALUE - 1))) |=> (Q == $past(DATA_IN))
    );

    // Q increments by one when LOAD is low and terminal count is not reached.
    check_increment_when_not_wrapping: assert property (
        @(posedge CLK) disable iff (CLR_B) (!LOAD && (Q != (MAX_VALUE - 1))) |=> (Q == ($past(Q) + 5'd1))
    );

    // Q wraps to zero when terminal count is reached and LOAD is low.
    check_wrap_to_zero_at_terminal_count: assert property (
        @(posedge CLK) disable iff (CLR_B) (!LOAD && (Q == (MAX_VALUE - 1))) |=> (Q == 5'd0)
    );

endmodule