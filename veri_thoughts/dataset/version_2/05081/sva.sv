module moore_state_machine_sva (
    input logic       clk,
    input logic       reset,
    input logic       input_bit,
    input logic [1:0] state
);

    // Active-low reset forces state to 00.
    check_reset_forces_state_00: assert property (
        @(posedge clk) (!reset) |-> (state == 2'b00)
    );

    // State 00 with input 0 transitions to 01.
    check_state_00_input_0_to_01: assert property (
        @(posedge clk) disable iff (!reset)
        ((state == 2'b00) && (input_bit == 1'b0)) |=> (state == 2'b01)
    );

    // State 00 with input 1 stays at 00.
    check_state_00_input_1_stays_00: assert property (
        @(posedge clk) disable iff (!reset)
        ((state == 2'b00) && (input_bit == 1'b1)) |=> (state == 2'b00)
    );

    // State 01 with input 0 transitions to 10.
    check_state_01_input_0_to_10: assert property (
        @(posedge clk) disable iff (!reset)
        ((state == 2'b01) && (input_bit == 1'b0)) |=> (state == 2'b10)
    );

    // State 01 with input 1 stays at 01.
    check_state_01_input_1_stays_01: assert property (
        @(posedge clk) disable iff (!reset)
        ((state == 2'b01) && (input_bit == 1'b1)) |=> (state == 2'b01)
    );

    // State 10 with input 0 transitions to 01.
    check_state_10_input_0_to_01: assert property (
        @(posedge clk) disable iff (!reset)
        ((state == 2'b10) && (input_bit == 1'b0)) |=> (state == 2'b01)
    );

    // State 10 with input 1 stays at 10.
    check_state_10_input_1_stays_10: assert property (
        @(posedge clk) disable iff (!reset)
        ((state == 2'b10) && (input_bit == 1'b1)) |=> (state == 2'b10)
    );

    // Unhandled encoding 11 holds its value.
    check_state_11_holds_value: assert property (
        @(posedge clk) disable iff (!reset)
        (state == 2'b11) |=> (state == 2'b11)
    );

endmodule