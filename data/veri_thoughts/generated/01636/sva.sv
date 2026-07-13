module button_counter_sva (
    input logic        BTN,
    input logic [3:0]  COUNT
);
    // When previous COUNT was not 15, next BTN edge increments by 1.
    check_inc_when_prev_not_15: assert property (
        @(posedge BTN) 1'b1 |=> ( ($past(COUNT) != 4'd15) |-> (COUNT == $past(COUNT) + 4'd1) )
    );

    // When previous COUNT was 15, next BTN edge wraps to 0.
    check_wrap_when_prev_15: assert property (
        @(posedge BTN) 1'b1 |=> ( ($past(COUNT) == 4'd15) |-> (COUNT == 4'd0) )
    );

    // COUNT must change on every BTN rising edge.
    check_count_changes_each_pulse: assert property (
        @(posedge BTN) 1'b1 |=> ( ($past(COUNT) == $past(COUNT)) |-> (COUNT != $past(COUNT)) )
    );

    // After 16 BTN edges, COUNT repeats its value (mod-16 behavior).
    check_period_16: assert property (
        @(posedge BTN) 1'b1 |-> ##16 (COUNT == $past(COUNT,16))
    );
endmodule