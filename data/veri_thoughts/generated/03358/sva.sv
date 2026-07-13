module dff_asynchronous_set_sva (
    input logic CLK,
    input logic D,
    input logic Q,
    input logic SET_B
);

    // Low SET_B overrides D and forces Q high on the next cycle.
    check_set_overrides_data: assert property (
        @(posedge CLK) (SET_B == 1'b0) |=> (Q == 1'b1)
    );

    // With SET_B high and D low, Q captures 0 on the next cycle.
    check_capture_zero: assert property (
        @(posedge CLK) (SET_B == 1'b1) && (D == 1'b0) |=> (Q == 1'b0)
    );

    // With SET_B high and D high, Q captures 1 on the next cycle.
    check_capture_one: assert property (
        @(posedge CLK) (SET_B == 1'b1) && (D == 1'b1) |=> (Q == 1'b1)
    );

endmodule