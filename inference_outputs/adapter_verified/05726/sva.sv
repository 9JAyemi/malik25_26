module binary_counter_sva (
    input logic CLK,
    input logic CLR_B,
    input logic LOAD,
    input logic [4:0] DATA_IN,
    input logic [4:0] Q
);

// CLR_B clears Q to 0 on the next cycle.
    check_clear_sets_zero: assert property (
        @(posedge CLK) CLR_B |=> (Q == 5'd0)
    );

// LOAD captures DATA_IN into Q on the next cycle when CLR_B is low.
    check_load_captures_data: assert property (
        @(posedge CLK) disable iff (CLR_B) LOAD |=> (Q == $past(DATA_IN))
    );

// When not clearing or loading and Q is not at MAX_VALUE, Q increments by 1.
    check_increment_when_idle: assert property (
        @(posedge CLK) disable iff (CLR_B) (!LOAD && (Q != MAX_VALUE)) |=> (Q == ($past(Q) + 5'd1))
    );

// When not clearing or loading and Q reaches MAX_VALUE, Q wraps to 0.
    check_wrap_at_max: assert property (
        @(posedge CLK) disable iff (CLR_B) (!LOAD && (Q == MAX_VALUE)) |=> (Q == 5'd0)
    );

// Q can only be 0 when cleared or wrapped from MAX_VALUE.
    check_zero_only_on_clear_or_wrap: assert property (
        @(posedge CLK) (Q == 5'd0) |-> (CLR_B || ($past(Q) == MAX_VALUE))
    );

// LOAD has priority over the idle increment rule when both are asserted.
    check_load_priority_over_increment: assert property (
        @(posedge CLK) (LOAD && (Q != MAX_VALUE)) |=> (Q == $past(DATA_IN))
    );

endmodule
