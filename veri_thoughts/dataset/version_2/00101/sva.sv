module MUX4X1_sva (
    input logic       clk,
    input logic [3:0] input_signals,
    input logic [1:0] select_signals,
    input logic       output_signal
);

    // Select 00 routes input_signals[0] to the output.
    check_select_00_routes_input0: assert property (
        @(posedge clk)
        (select_signals === 2'b00) |-> (output_signal === input_signals[0])
    );

    // Select 01 routes input_signals[1] to the output.
    check_select_01_routes_input1: assert property (
        @(posedge clk)
        (select_signals === 2'b01) |-> (output_signal === input_signals[1])
    );

    // Select 10 routes input_signals[2] to the output.
    check_select_10_routes_input2: assert property (
        @(posedge clk)
        (select_signals === 2'b10) |-> (output_signal === input_signals[2])
    );

    // Select 11 routes input_signals[3] to the output.
    check_select_11_routes_input3: assert property (
        @(posedge clk)
        (select_signals === 2'b11) |-> (output_signal === input_signals[3])
    );

    // With select 00 held, a stable input_signals[0] keeps the output stable.
    check_select_00_stable_input0_keeps_output_stable: assert property (
        @(posedge clk)
        ($stable(select_signals) && (select_signals === 2'b00) && $stable(input_signals[0])) |-> $stable(output_signal)
    );

    // With select 01 held, a stable input_signals[1] keeps the output stable.
    check_select_01_stable_input1_keeps_output_stable: assert property (
        @(posedge clk)
        ($stable(select_signals) && (select_signals === 2'b01) && $stable(input_signals[1])) |-> $stable(output_signal)
    );

    // With select 10 held, a stable input_signals[2] keeps the output stable.
    check_select_10_stable_input2_keeps_output_stable: assert property (
        @(posedge clk)
        ($stable(select_signals) && (select_signals === 2'b10) && $stable(input_signals[2])) |-> $stable(output_signal)
    );

    // With select 11 held, a stable input_signals[3] keeps the output stable.
    check_select_11_stable_input3_keeps_output_stable: assert property (
        @(posedge clk)
        ($stable(select_signals) && (select_signals === 2'b11) && $stable(input_signals[3])) |-> $stable(output_signal)
    );

endmodule