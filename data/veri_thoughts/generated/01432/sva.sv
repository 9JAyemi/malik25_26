module input_output_module_sva (
    input logic        CLK,
    input logic [6:0]  Q,

    // Internal DUT signals (for bind-by-name)
    input logic [6:0]  inputs_reg,
    input logic [6:0]  inputs_delayed,
    input logic [6:0]  delay_counter,
    input logic [2:0]  input_counter,
    input logic [1:0]  state_counter,
    input logic [6:0]  inputs_pattern_0,
    input logic [6:0]  inputs_pattern_1,
    input logic [6:0]  inputs_pattern_2,
    input logic        Q_delayed,
    input logic        Q_delayed_reg
);
    // Q_delayed is a direct alias of Q.
    check_q_delayed_alias: assert property (
        @(posedge CLK) Q_delayed == Q
    );

    // Q_delayed_reg captures Q with one-cycle latency.
    check_q_delayed_reg_captures_q: assert property (
        @(posedge CLK) Q_delayed_reg == $past(Q)
    );

    // inputs_reg captures Q each cycle.
    check_inputs_reg_captures_q: assert property (
        @(posedge CLK) inputs_reg == $past(Q)
    );

    // inputs_delayed is the bit-reversed view of inputs_reg.
    check_inputs_delayed_is_reverse: assert property (
        @(posedge CLK) inputs_delayed == {inputs_reg[0],inputs_reg[1],inputs_reg[2],inputs_reg[3],inputs_reg[4],inputs_reg[5],inputs_reg[6]}
    );

    // delay_counter increments by 1 when previous value was not 20.
    check_delay_counter_incr: assert property (
        @(posedge CLK) ($past(delay_counter) != 7'd20) |-> (delay_counter == $past(delay_counter) + 7'd1)
    );

    // delay_counter resets to 0 when previous value was 20.
    check_delay_counter_rollover: assert property (
        @(posedge CLK) ($past(delay_counter) == 7'd20) |-> (delay_counter == 7'd0)
    );

    // input_counter holds unless delay_counter hit 20.
    check_input_counter_holds_without_tick: assert property (
        @(posedge CLK) ($past(delay_counter) != 7'd20) |-> (input_counter == $past(input_counter))
    );

    // input_counter increments when delay_counter hit 20 and not at 7.
    check_input_counter_increments_on_tick: assert property (
        @(posedge CLK) ($past(delay_counter) == 7'd20 && $past(input_counter) != 3'd7) |-> (input_counter == $past(input_counter) + 3'd1)
    );

    // input_counter resets to 0 when it was 7 and delay_counter hit 20.
    check_input_counter_rollover: assert property (
        @(posedge CLK) ($past(delay_counter) == 7'd20 && $past(input_counter) == 3'd7) |-> (input_counter == 3'd0)
    );

    // state_counter holds unless input_counter was 7 and delay_counter hit 20.
    check_state_counter_holds_without_roll: assert property (
        @(posedge CLK) !($past(delay_counter) == 7'd20 && $past(input_counter) == 3'd7) |-> (state_counter == $past(state_counter))
    );

    // state_counter increments when roll event occurs and previous value was not 3.
    check_state_counter_increments: assert property (
        @(posedge CLK) ($past(delay_counter) == 7'd20 && $past(input_counter) == 3'd7 && $past(state_counter) != 2'd3) |-> (state_counter == $past(state_counter) + 2'd1)
    );

    // state_counter resets to 0 when roll event occurs and previous value was 3.
    check_state_counter_resets_to_zero: assert property (
        @(posedge CLK) ($past(delay_counter) == 7'd20 && $past(input_counter) == 3'd7 && $past(state_counter) == 2'd3) |-> (state_counter == 2'd0)
    );

    // When previous state was 0, Q is driven by inputs_pattern_0.
    check_q_when_state0: assert property (
        @(posedge CLK) ($past(state_counter) == 2'd0) |-> (Q == inputs_pattern_0)
    );

    // When previous state was 1, Q is driven by inputs_pattern_1.
    check_q_when_state1: assert property (
        @(posedge CLK) ($past(state_counter) == 2'd1) |-> (Q == inputs_pattern_1)
    );

    // When previous state was 3, Q holds its previous value (no assignment in case).
    check_q_holds_when_state3: assert property (
        @(posedge CLK) ($past(state_counter) == 2'd3) |-> (Q == $past(Q))
    );
endmodule