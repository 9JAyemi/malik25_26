module up_down_counter_sva (
    input logic up_down,
    input logic clear,
    input logic load,
    input logic [3:0] data_in,
    input logic clk,
    input logic [3:0] count_out
);

// Clear low forces the counter to zero.
    check_clear_forces_zero: assert property (
        @(posedge clk) !clear |-> (count_out == 4'b0000)
    );

// Load captures data_in when clear is high and load is high.
    check_load_captures_data: assert property (
        @(posedge clk) disable iff (!clear) (load == 1'b1) |=> (count_out == $past(data_in))
    );

// Up mode increments the counter when clear and load are high.
    check_up_mode_increments: assert property (
        @(posedge clk) disable iff (!clear) (load == 1'b0) && (up_down == 1'b1) |=> (count_out == ($past(count_out) + 4'b0001))
    );

// Down mode decrements the counter when clear and load are high.
    check_down_mode_decrements: assert property (
        @(posedge clk) disable iff (!clear) (load == 1'b0) && (up_down == 1'b0) |=> (count_out == ($past(count_out) - 4'b0001))
    );

// With clear high and no load, the counter holds its value.
    check_hold_when_idle: assert property (
        @(posedge clk) disable iff (!clear) (load == 1'b0) && (up_down == 1'b0) |=> (count_out == $past(count_out))
    );

// Incrementing from 4'hF wraps to 4'h0.
    check_up_wrap_from_max: assert property (
        @(posedge clk) disable iff (!clear) (load == 1'b0) && (up_down == 1'b1) && (count_out == 4'hF) |=> (count_out == 4'h0)
    );

// Decrementing from 4'h0 wraps to 4'hF.
    check_down_wrap_from_zero: assert property (
        @(posedge clk) disable iff (!clear) (load == 1'b0) && (up_down == 1'b0) && (count_out == 4'h0) |=> (count_out == 4'hF)
    );

endmodule
