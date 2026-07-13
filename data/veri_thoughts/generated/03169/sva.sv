module top_module_sva (
    input logic       clk,
    input logic       reset,
    input logic       up_down,
    input logic       parallel_load,
    input logic [6:0] LOAD_IN,
    input logic [6:0] ripple_counter_out,
    input logic       ser_out,
    input logic [6:0] parallel_load_data,
    input logic [6:0] ripple_counter,
    input logic [2:0] shift_register_data
);

    // Counter loads LOAD_IN[3:0] with zero-extension when parallel_load is high.
    check_counter_load_zero_extend: assert property (
        @(posedge clk) disable iff (reset)
        parallel_load |=> (ripple_counter == {3'b000, $past(LOAD_IN[3:0])})
    );

    // Counter increments by one when not loading and up_down is high.
    check_counter_increment: assert property (
        @(posedge clk) disable iff (reset)
        (!parallel_load && up_down) |=> (ripple_counter == ($past(ripple_counter) + 7'd1))
    );

    // Counter decrements by one when not loading and up_down is low.
    check_counter_decrement: assert property (
        @(posedge clk) disable iff (reset)
        (!parallel_load && !up_down) |=> (ripple_counter == ($past(ripple_counter) - 7'd1))
    );

    // Shift register clears to zero when parallel_load is high.
    check_shift_clear_on_load: assert property (
        @(posedge clk) disable iff (reset)
        parallel_load |=> (shift_register_data == 3'b000)
    );

    // Shift register shifts left and inserts ripple_counter[6] when not loading.
    check_shift_shift_behavior: assert property (
        @(posedge clk) disable iff (reset)
        (!parallel_load) |=> (shift_register_data == {$past(shift_register_data[1:0]), $past(ripple_counter[6])})
    );

    // Top-level load register captures LOAD_IN when parallel_load is high.
    check_parallel_load_data_capture: assert property (
        @(posedge clk) disable iff (reset)
        parallel_load |=> (parallel_load_data == $past(LOAD_IN))
    );

    // Top-level load register holds its value when parallel_load is low.
    check_parallel_load_data_hold: assert property (
        @(posedge clk) disable iff (reset)
        (!parallel_load) |=> (parallel_load_data == $past(parallel_load_data))
    );

    // Top-level counter output registers the internal counter value every cycle.
    check_ripple_counter_out_tracks_counter: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (ripple_counter_out == $past(ripple_counter))
    );

    // Serial output always reflects bit 2 of the shift register.
    check_ser_out_mapping: assert property (
        @(posedge clk) disable iff (reset)
        (ser_out == shift_register_data[2])
    );

    // Counter is zero on the first cycle after reset is released.
    check_counter_zero_after_reset: assert property (
        @(posedge clk) disable iff (reset)
        ((!$initstate) && $past(reset)) |-> (ripple_counter == 7'b0)
    );

    // Top-level registered outputs are zero on the first cycle after reset is released.
    check_top_regs_zero_after_reset: assert property (
        @(posedge clk) disable iff (reset)
        ((!$initstate) && $past(reset)) |-> ((ripple_counter_out == 7'b0) && (parallel_load_data == 7'b0))
    );

endmodule