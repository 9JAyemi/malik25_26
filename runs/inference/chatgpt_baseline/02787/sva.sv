module twos_complement_sva (
    input logic clk,
    input logic [3:0] binary,
    input logic [3:0] twos_comp
);
    // twos_comp equals (~binary + 1) modulo 16.
    check_twos_comp_definition: assert property (
        @(posedge clk) twos_comp == ((~binary + 4'b0001)[3:0])
    );

    // binary + twos_comp wraps to zero modulo 16.
    check_additive_inverse_mod16: assert property (
        @(posedge clk) ((binary + twos_comp)[3:0]) == 4'b0000
    );

    // If input is zero, output is zero.
    check_zero_maps_to_zero: assert property (
        @(posedge clk) (binary == 4'b0000) |-> (twos_comp == 4'b0000)
    );

    // If input is 8 (1000), output is also 8 (fixed point in 4-bit 2's comp).
    check_neg8_fixed_point: assert property (
        @(posedge clk) (binary == 4'b1000) |-> (twos_comp == 4'b1000)
    );

    // 1 maps to 15.
    check_one_maps_to_f: assert property (
        @(posedge clk) (binary == 4'b0001) |-> (twos_comp == 4'b1111)
    );

    // 15 maps to 1.
    check_f_maps_to_one: assert property (
        @(posedge clk) (binary == 4'b1111) |-> (twos_comp == 4'b0001)
    );

    // Inverse relation: binary equals (~twos_comp + 1) modulo 16.
    check_double_complement_relation: assert property (
        @(posedge clk) binary == ((~twos_comp + 4'b0001)[3:0])
    );

    // If input is stable across a cycle, output is stable.
    check_stability_when_input_stable: assert property (
        @(posedge clk) $stable(binary) |-> $stable(twos_comp)
    );

    // If input changes across a cycle, output changes (bijective mapping).
    check_change_propagates: assert property (
        @(posedge clk) $changed(binary) |-> $changed(twos_comp)
    );

    // LSB is preserved by two's complement.
    check_lsb_preserved: assert property (
        @(posedge clk) twos_comp[0] == binary[0]
    );
endmodule