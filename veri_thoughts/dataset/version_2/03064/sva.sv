module openhmc_counter48_sva #(
    parameter DATASIZE = 16
) (
    input logic                 clk,
    input logic                 res_n,
    input logic                 increment,
    input logic                 load_enable,
    input logic [DATASIZE-1:0]  value
);

    // A sampled reset cycle forces the counter output to zero by the next sample.
    check_reset_clears_value: assert property (
        @(posedge clk)
        (!res_n) |=> (value == {DATASIZE{1'b0}})
    );

    // With no pending load and no increment, the counter holds its value.
    check_hold_when_no_load_pending_and_no_increment: assert property (
        @(posedge clk) disable iff (!res_n)
        ($past(res_n) && !$past(load_enable) && !increment) |=> (value == $past(value))
    );

    // With no pending load and increment asserted, the counter increments by one.
    check_increment_when_no_load_pending: assert property (
        @(posedge clk) disable iff (!res_n)
        ($past(res_n) && !$past(load_enable) && increment) |=> (value == ($past(value) + 1'b1))
    );

    // A pending load with no increment clears the counter to zero.
    check_clear_when_load_was_pending_and_no_increment: assert property (
        @(posedge clk) disable iff (!res_n)
        ($past(res_n) && $past(load_enable) && !increment) |=> (value == {DATASIZE{1'b0}})
    );

    // A pending load with increment asserted sets the counter to one.
    check_set_one_when_load_was_pending_and_increment: assert property (
        @(posedge clk) disable iff (!res_n)
        ($past(res_n) && $past(load_enable) && increment) |=> (value == ({DATASIZE{1'b0}} + 1'b1))
    );

endmodule