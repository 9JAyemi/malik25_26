module priority_encoder_4to2_sva (
    input logic [3:0] I,
    input logic [1:0] Y
);

    // No RTL clock or reset; sample this combinational mapping on $global_clock.

    // Input 0001 produces output 00.
    check_input_0001_maps_to_00: assert property (
        @($global_clock) (I == 4'b0001) |-> (Y == 2'b00)
    );

    // Input 0010 produces output 01.
    check_input_0010_maps_to_01: assert property (
        @($global_clock) (I == 4'b0010) |-> (Y == 2'b01)
    );

    // Input 0100 produces output 10.
    check_input_0100_maps_to_10: assert property (
        @($global_clock) (I == 4'b0100) |-> (Y == 2'b10)
    );

    // Input 1000 produces output 11.
    check_input_1000_maps_to_11: assert property (
        @($global_clock) (I == 4'b1000) |-> (Y == 2'b11)
    );

    // All other input patterns produce the default output 00.
    check_other_inputs_default_to_00: assert property (
        @($global_clock)
        ((I != 4'b0001) && (I != 4'b0010) && (I != 4'b0100) && (I != 4'b1000))
        |-> (Y == 2'b00)
    );

    // Output 01 can only come from input 0010.
    check_output_01_only_from_0010: assert property (
        @($global_clock) (Y == 2'b01) |-> (I == 4'b0010)
    );

    // Output 10 can only come from input 0100.
    check_output_10_only_from_0100: assert property (
        @($global_clock) (Y == 2'b10) |-> (I == 4'b0100)
    );

    // Output 11 can only come from input 1000.
    check_output_11_only_from_1000: assert property (
        @($global_clock) (Y == 2'b11) |-> (I == 4'b1000)
    );

    // Output 00 never occurs for inputs that map to nonzero codes.
    check_output_00_excludes_nonzero_mappings: assert property (
        @($global_clock) (Y == 2'b00) |-> ((I != 4'b0010) && (I != 4'b0100) && (I != 4'b1000))
    );

endmodule