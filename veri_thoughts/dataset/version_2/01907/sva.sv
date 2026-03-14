module and_module_sva (
    input logic [7:0] i_bus1,
    input logic [7:0] i_bus2,
    input logic [7:0] o_bus
);
    // No clock/reset in RTL; combinational AND. Sample on posedge of i_bus1[0].

    // Output equals bitwise AND of inputs (vector-level).
    check_and_vector: assert property (
        @(posedge i_bus1[0]) o_bus == (i_bus1 & i_bus2)
    );

    // Output is a subset of i_bus1 (no 1s where i_bus1 has 0s).
    check_output_subset_input1: assert property (
        @(posedge i_bus1[0]) (o_bus & ~i_bus1) == 8'h00
    );

    // Output is a subset of i_bus2 (no 1s where i_bus2 has 0s).
    check_output_subset_input2: assert property (
        @(posedge i_bus1[0]) (o_bus & ~i_bus2) == 8'h00
    );

    // When i_bus1 is all 1s, o_bus passes through i_bus2.
    check_allones_i_bus1_passthrough: assert property (
        @(posedge i_bus1[0]) (i_bus1 == 8'hFF) |-> (o_bus == i_bus2)
    );

    // When i_bus2 is all 1s, o_bus passes through i_bus1.
    check_allones_i_bus2_passthrough: assert property (
        @(posedge i_bus1[0]) (i_bus2 == 8'hFF) |-> (o_bus == i_bus1)
    );

    // When i_bus1 is all 0s, o_bus is all 0s.
    check_allzeros_i_bus1_zeroout: assert property (
        @(posedge i_bus1[0]) (i_bus1 == 8'h00) |-> (o_bus == 8'h00)
    );

    // When i_bus2 is all 0s, o_bus is all 0s.
    check_allzeros_i_bus2_zeroout: assert property (
        @(posedge i_bus1[0]) (i_bus2 == 8'h00) |-> (o_bus == 8'h00)
    );

    // LSB equals AND of corresponding input bits.
    check_bit0_and: assert property (
        @(posedge i_bus1[0]) o_bus[0] == (i_bus1[0] & i_bus2[0])
    );

    // MSB equals AND of corresponding input bits.
    check_bit7_and: assert property (
        @(posedge i_bus1[0]) o_bus[7] == (i_bus1[7] & i_bus2[7])
    );

    // Output also equals AND with reversed operand order (commutativity).
    check_and_commutative_form: assert property (
        @(posedge i_bus1[0]) o_bus == (i_bus2 & i_bus1)
    );
endmodule