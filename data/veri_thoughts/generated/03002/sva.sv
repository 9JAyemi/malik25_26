module synchronous_counter_sva #(
    parameter DataSize = 4
) (
    input  logic                  clock,
    input  logic                  reset,
    input  logic                  enable,
    input  logic                  load,
    input  logic [DataSize-1:0]   data_in,
    input  logic [DataSize-1:0]   data_out
);

    // Active-low reset forces the counter output to zero.
    check_reset_clears_output: assert property (
        @(posedge clock)
        !reset |-> (data_out == '0)
    );

    // A sampled reset cycle leaves the next sampled output at zero.
    check_reset_keeps_output_zero_next_cycle: assert property (
        @(posedge clock)
        !reset |=> (data_out == '0)
    );

    // When enabled and load is high, the next output reflects the prior input unless reset intervened.
    check_load_updates_output: assert property (
        @(posedge clock) disable iff (!reset)
        (enable && load) |=> ((data_out == $past(data_in)) || (data_out == '0))
    );

    // When enabled and load is low, the next output increments unless reset intervened.
    check_enable_increments_output: assert property (
        @(posedge clock) disable iff (!reset)
        (enable && !load) |=> ((data_out == ($past(data_out) + {{(DataSize-1){1'b0}}, 1'b1})) || (data_out == '0))
    );

    // When enable is low, the output holds its value unless reset intervened.
    check_disable_holds_output: assert property (
        @(posedge clock) disable iff (!reset)
        (!enable) |=> ((data_out == $past(data_out)) || (data_out == '0))
    );

    // Load is ignored when enable is low.
    check_load_ignored_when_disabled: assert property (
        @(posedge clock) disable iff (!reset)
        (!enable && load) |=> ((data_out == $past(data_out)) || (data_out == '0))
    );

endmodule