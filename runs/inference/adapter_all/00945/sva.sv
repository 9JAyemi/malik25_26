module control_module_sva (
    input logic [3:0] input_1,
    input logic [1:0] input_2,
    input logic       input_3,
    input logic       input_4,
    input logic       input_5,
    input logic       input_6,
    input logic       input_7,
    input logic       input_8,
    input logic       output_1
);

    // No RTL clock or reset; sample combinational behavior on the formal global clock.

    // input_1 0 maps output_1 to 0.
    check_map_input_1_0: assert property (
        @($global_clock) (input_1 == 4'd0) |-> (output_1 == 1'b0)
    );

    // input_1 1 maps output_1 to input_3.
    check_map_input_1_1: assert property (
        @($global_clock) (input_1 == 4'd1) |-> (output_1 == input_3)
    );

    // input_1 2 maps output_1 to input_4.
    check_map_input_1_2: assert property (
        @($global_clock) (input_1 == 4'd2) |-> (output_1 == input_4)
    );

    // input_1 3 maps output_1 to input_5.
    check_map_input_1_3: assert property (
        @($global_clock) (input_1 == 4'd3) |-> (output_1 == input_5)
    );

    // input_1 4 maps output_1 to input_6.
    check_map_input_1_4: assert property (
        @($global_clock) (input_1 == 4'd4) |-> (output_1 == input_6)
    );

    // input_1 5 maps output_1 to input_7.
    check_map_input_1_5: assert property (
        @($global_clock) (input_1 == 4'd5) |-> (output_1 == input_7)
    );

    // input_1 6 maps output_1 to input_8.
    check_map_input_1_6: assert property (
        @($global_clock) (input_1 == 4'd6) |-> (output_1 == input_8)
    );

    // input_1 7 maps output_1 to input_2.
    check_map_input_1_7: assert property (
        @($global_clock) (input_1 == 4'd7) |-> (output_1 == input_2)
    );

    // input_1 8 through 15 map output_1 to 0.
    check_map_input_1_default: assert property (
        @($global_clock) (input_1 >= 4'd8) |-> (output_1 == 1'b0)
    );

endmodule