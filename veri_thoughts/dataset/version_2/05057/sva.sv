module _2bit_up_counter_with_synch_load_enable_clear_sva (
    input logic       Clock,
    input logic       Clear,
    input logic       Enable,
    input logic       Load,
    input logic [1:0] Q
);

    // Clear synchronously forces the counter to zero.
    check_clear_forces_zero: assert property (
        @(posedge Clock) Clear |=> (Q == 2'b00)
    );

    // Load sets the counter to 2'b11 when clear is inactive.
    check_load_sets_q_to_11: assert property (
        @(posedge Clock) disable iff (Clear) Load |=> (Q == 2'b11)
    );

    // With no control active, the counter holds its value.
    check_idle_holds_q: assert property (
        @(posedge Clock) disable iff (Clear) (!Load && !Enable) |=> (Q == $past(Q))
    );

    // Enable increments 2'b00 to 2'b01.
    check_enable_00_to_01: assert property (
        @(posedge Clock) disable iff (Clear) (!Load && Enable && (Q == 2'b00)) |=> (Q == 2'b01)
    );

    // Enable increments 2'b01 to 2'b10.
    check_enable_01_to_10: assert property (
        @(posedge Clock) disable iff (Clear) (!Load && Enable && (Q == 2'b01)) |=> (Q == 2'b10)
    );

    // Enable increments 2'b10 to 2'b11.
    check_enable_10_to_11: assert property (
        @(posedge Clock) disable iff (Clear) (!Load && Enable && (Q == 2'b10)) |=> (Q == 2'b11)
    );

    // Enable wraps 2'b11 back to 2'b00.
    check_enable_11_to_00: assert property (
        @(posedge Clock) disable iff (Clear) (!Load && Enable && (Q == 2'b11)) |=> (Q == 2'b00)
    );

endmodule