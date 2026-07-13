module onlyonecycle_assertions (
    input logic       trigger,
    input logic       output_xhdl0,
    input logic       globalreset,
    input logic       clk,
    input logic [1:0] state,
    input logic [1:0] next_state,
    input logic [0:0] count,
    input logic [0:0] temp_count
);

    // Reset forces the state and count registers to zero.
    reset_clears_state_and_count: assert property (
        @(posedge clk) globalreset |-> ((state == 2'd0) && (count == 1'b0))
    );

    // Reset forces the output low.
    reset_drives_output_low: assert property (
        @(posedge clk) globalreset |-> (output_xhdl0 == 1'b0)
    );

    // In state 0 with no trigger, output stays low and the FSM stays in state 0.
    idle_decode_no_trigger: assert property (
        @(posedge clk) disable iff (globalreset)
        ((state == 2'd0) && (trigger == 1'b0)) |-> ((output_xhdl0 == 1'b0) && (next_state == 2'd0) && (temp_count == 1'b0))
    );

    // In state 0 with trigger high, output stays low and the FSM targets state 1.
    idle_decode_trigger: assert property (
        @(posedge clk) disable iff (globalreset)
        ((state == 2'd0) && (trigger == 1'b1)) |-> ((output_xhdl0 == 1'b0) && (next_state == 2'd1) && (temp_count == 1'b0))
    );

    // In state 1 with count 0, output is high and the FSM targets state 2.
    pulse_decode_count_zero: assert property (
        @(posedge clk) disable iff (globalreset)
        ((state == 2'd1) && (count == 1'b0)) |-> ((output_xhdl0 == 1'b1) && (next_state == 2'd2) && (temp_count == 1'b1))
    );

    // In state 1 with count 1, output is high and the FSM stays in state 1.
    pulse_decode_count_one: assert property (
        @(posedge clk) disable iff (globalreset)
        ((state == 2'd1) && (count == 1'b1)) |-> ((output_xhdl0 == 1'b1) && (next_state == 2'd1) && (temp_count == 1'b0))
    );

    // In state 2 with trigger low, output is low and the FSM targets state 0.
    holdoff_decode_trigger_low: assert property (
        @(posedge clk) disable iff (globalreset)
        ((state == 2'd2) && (trigger == 1'b0)) |-> ((output_xhdl0 == 1'b0) && (next_state == 2'd0))
    );

    // In state 2 with trigger high, output is low and the FSM stays in state 2.
    holdoff_decode_trigger_high: assert property (
        @(posedge clk) disable iff (globalreset)
        ((state == 2'd2) && (trigger == 1'b1)) |-> ((output_xhdl0 == 1'b0) && (next_state == 2'd2))
    );

    // In state 0 without trigger, the next cycle remains idle.
    idle_no_trigger_stays_idle: assert property (
        @(posedge clk) disable iff (globalreset)
        ((state == 2'd0) && (trigger == 1'b0)) |=> ((state == 2'd0) && (count == 1'b0) && (output_xhdl0 == 1'b0))
    );

    // A trigger in state 0 produces the pulse state on the next cycle.
    idle_trigger_enters_pulse: assert property (
        @(posedge clk) disable iff (globalreset)
        ((state == 2'd0) && (trigger == 1'b1)) |=> ((state == 2'd1) && (count == 1'b0) && (output_xhdl0 == 1'b1))
    );

    // State 1 with count 0 exits to state 2 on the next cycle.
    pulse_count_zero_enters_holdoff: assert property (
        @(posedge clk) disable iff (globalreset)
        ((state == 2'd1) && (count == 1'b0)) |=> ((state == 2'd2) && (count == 1'b1) && (output_xhdl0 == 1'b0))
    );

    // State 1 with count 1 stays in state 1 and decrements count.
    pulse_count_one_repeats_pulse: assert property (
        @(posedge clk) disable iff (globalreset)
        ((state == 2'd1) && (count == 1'b1)) |=> ((state == 2'd1) && (count == 1'b0) && (output_xhdl0 == 1'b1))
    );

    // In state 2, dropping trigger returns the FSM to idle on the next cycle.
    holdoff_trigger_low_returns_idle: assert property (
        @(posedge clk) disable iff (globalreset)
        ((state == 2'd2) && (trigger == 1'b0)) |=> ((state == 2'd0) && (output_xhdl0 == 1'b0))
    );

    // In state 2, holding trigger high keeps the FSM in state 2.
    holdoff_trigger_high_stays_holdoff: assert property (
        @(posedge clk) disable iff (globalreset)
        ((state == 2'd2) && (trigger == 1'b1)) |=> ((state == 2'd2) && (output_xhdl0 == 1'b0))
    );

endmodule