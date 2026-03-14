module logicblock_counter_sva #(
    parameter DATA_WIDTH = 32
) (
    input  logic                     clock,
    input  logic                     resetn,
    input  logic                     i_start,
    input  logic [DATA_WIDTH-1:0]    i_size,
    input  logic [DATA_WIDTH-1:0]    o_dataout,
    input  logic                     o_dataout_valid,
    input  logic                     i_dataout_stall,
    input  logic                     i_counter_reset
);

    // Async active-low reset drives counter output to zero.
    reset_clears_output: assert property (
        @(posedge clock) (!resetn) |-> (o_dataout == '0)
    );

    // Counter reset clears output on the next cycle.
    sync_counter_reset_next_zero: assert property (
        @(posedge clock) disable iff (!resetn) i_counter_reset |=> (o_dataout == '0)
    );

    // When enabled (start & not stalled & below size) and not resetting, counter increments by 1.
    increment_when_enabled: assert property (
        @(posedge clock) disable iff (!resetn)
            (!i_counter_reset && i_start && !i_dataout_stall && (o_dataout < i_size))
            |=> (o_dataout == $past(o_dataout) + 1)
    );

    // When not taking the increment path and not resetting, output holds its value.
    hold_when_no_increment_condition: assert property (
        @(posedge clock) disable iff (!resetn)
            (!i_counter_reset && !(i_start && !i_dataout_stall && (o_dataout < i_size)))
            |=> $stable(o_dataout)
    );

    // Without counter reset, output changes per step only by 0 or +1.
    bounded_step_without_reset: assert property (
        @(posedge clock) disable iff (!resetn)
            (!i_counter_reset) |=> ((o_dataout == $past(o_dataout)) || (o_dataout == $past(o_dataout) + 1))
    );

    // o_dataout_valid equals its combinational definition.
    valid_definition: assert property (
        @(posedge clock) disable iff (!resetn)
            (o_dataout_valid == (i_start && !i_counter_reset && (o_dataout < i_size)))
    );

    // i_counter_reset forces o_dataout_valid LOW in the same cycle.
    valid_low_on_counter_reset: assert property (
        @(posedge clock) disable iff (!resetn) i_counter_reset |-> (o_dataout_valid == 1'b0)
    );

    // If start is LOW, o_dataout_valid must be LOW.
    valid_low_when_no_start: assert property (
        @(posedge clock) disable iff (!resetn) (!i_start) |-> (o_dataout_valid == 1'b0)
    );

    // If counter is not less than size, o_dataout_valid must be LOW.
    valid_low_when_not_less_than_size: assert property (
        @(posedge clock) disable iff (!resetn) (!(o_dataout < i_size)) |-> (o_dataout_valid == 1'b0)
    );

    // Stall blocks increment: when stalled and not resetting, output holds.
    hold_when_stalled: assert property (
        @(posedge clock) disable iff (!resetn)
            (!i_counter_reset && i_dataout_stall) |=> $stable(o_dataout)
    );

endmodule