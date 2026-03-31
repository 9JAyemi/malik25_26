module shift_register_sva (
    input logic       clk,
    input logic       areset,
    input logic       load,
    input logic       ena,
    input logic [3:0] data,
    input logic [3:0] q,
    input logic [3:0] shift_reg,
    input logic [3:0] shifted_value
);

    // Clock: clk
    // Reset: areset is asynchronous active-high
    // Logic: sequential shift_reg/q with combinational shifted_value

    // Reset clears the internal shift register.
    check_reset_clears_shift_reg: assert property (
        @(posedge clk) areset |-> (shift_reg == 4'b0000)
    );

    // Reset clears the output register.
    check_reset_clears_q: assert property (
        @(posedge clk) areset |-> (q == 4'b0000)
    );

    // shifted_value is always the zero-filled right shift of shift_reg.
    check_shifted_value_definition: assert property (
        @(posedge clk) disable iff (areset)
        shifted_value == {1'b0, shift_reg[3:1]}
    );

    // load has priority and loads data into shift_reg.
    check_shift_reg_load_behavior: assert property (
        @(posedge clk) disable iff (areset)
        load |=> (shift_reg == $past(data))
    );

    // Without load, ena shifts shift_reg right with zero fill.
    check_shift_reg_shift_behavior: assert property (
        @(posedge clk) disable iff (areset)
        (!load && ena) |=> (shift_reg == {1'b0, $past(shift_reg[3:1])})
    );

    // With neither load nor ena, shift_reg holds its value.
    check_shift_reg_hold_behavior: assert property (
        @(posedge clk) disable iff (areset)
        (!load && !ena) |=> (shift_reg == $past(shift_reg))
    );

    // q loads data only when both load and ena are high.
    check_q_load_when_load_and_ena: assert property (
        @(posedge clk) disable iff (areset)
        (load && ena) |=> (q == $past(data))
    );

    // Otherwise q takes the prior shifted_value.
    check_q_uses_prior_shifted_value_otherwise: assert property (
        @(posedge clk) disable iff (areset)
        !(load && ena) |=> (q == $past(shifted_value))
    );

    // When ena is high, q and shift_reg update to the same value.
    check_q_matches_shift_reg_after_enable: assert property (
        @(posedge clk) disable iff (areset)
        ena |=> (q == shift_reg)
    );

endmodule

bind shift_register shift_register_sva shift_register_sva_inst (
    .clk(clk),
    .areset(areset),
    .load(load),
    .ena(ena),
    .data(data),
    .q(q),
    .shift_reg(shift_reg),
    .shifted_value(shifted_value)
);