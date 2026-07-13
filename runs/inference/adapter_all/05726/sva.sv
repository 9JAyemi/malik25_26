module binary_counter_sva (
    input logic CLK,
    input logic CLR_B,
    input logic LOAD,
    input logic [4:0] DATA_IN,
    input logic [4:0] Q
);

    localparam logic [4:0] MAX_VALUE = 5'd15;

    // CLR_B forces Q to zero on the next clock.
    check_clear_sets_zero: assert property (
        @(posedge CLK) disable iff (1'b0)
        CLR_B |=> (Q == 5'd0)
    );

    // LOAD captures DATA_IN when CLR_B is low.
    check_load_captures_data: assert property (
        @(posedge CLK) disable iff (1'b0)
        (!CLR_B && LOAD) |=> (Q == $past(DATA_IN))
    );

    // Q increments by one when CLR_B and LOAD are low and Q is not at MAX_VALUE.
    check_increment_when_not_max: assert property (
        @(posedge CLK) disable iff (1'b0)
        (!CLR_B && !LOAD && (Q != MAX_VALUE)) |=> (Q == ($past(Q) + 5'd1))
    );

    // Q wraps to zero when CLR_B and LOAD are low and Q is at MAX_VALUE.
    check_wrap_when_max: assert property (
        @(posedge CLK) disable iff (1'b0)
        (!CLR_B && !LOAD && (Q == MAX_VALUE)) |=> (Q == 5'd0)
    );

    // LOAD has priority over the increment/wrap behavior.
    check_load_priority_over_increment: assert property (
        @(posedge CLK) disable iff (1'b0)
        (!CLR_B && LOAD && (Q == MAX_VALUE)) |=> (Q == $past(DATA_IN))
    );

endmodule