module twos_complement_sva (
    input  logic        CLK,
    input  logic        RESETn,
    input  logic [3:0]  binary,
    input  logic [3:0]  twos_comp
);
    // twos_comp must equal bitwise NOT of binary plus one (two's complement definition).
    check_twos_comp_equals_not_plus1: assert property (
        @(posedge CLK) disable iff (!RESETn) twos_comp == ((~binary) + 4'd1)
    );

    // Input plus output must sum to zero modulo 16 (carry is discarded in 4 bits).
    check_sum_with_input_is_zero_mod16: assert property (
        @(posedge CLK) disable iff (!RESETn) (((twos_comp + binary) & 4'hF) == 4'd0)
    );

    // Input zero maps to output zero.
    check_zero_maps_to_zero: assert property (
        @(posedge CLK) disable iff (!RESETn) (binary == 4'd0) |-> (twos_comp == 4'd0)
    );

    // Only input zero produces output zero.
    check_only_zero_maps_to_zero: assert property (
        @(posedge CLK) disable iff (!RESETn) (twos_comp == 4'd0) |-> (binary == 4'd0)
    );

    // Input 0x8 (1000) is a fixed point of two's complement.
    check_minneg_fixed_point: assert property (
        @(posedge CLK) disable iff (!RESETn) (binary == 4'd8) |-> (twos_comp == 4'd8)
    );

    // If output equals input, the value must be 0 or 8 (the only fixed points).
    check_only_fixed_points_are_0_or_8: assert property (
        @(posedge CLK) disable iff (!RESETn) (twos_comp == binary) |-> ((binary == 4'd0) || (binary == 4'd8))
    );

    // Specific mapping: input 0xF maps to 0x1.
    check_allones_maps_to_one: assert property (
        @(posedge CLK) disable iff (!RESETn) (binary == 4'hF) |-> (twos_comp == 4'h1)
    );

    // Specific mapping: input 0x1 maps to 0xF.
    check_one_maps_to_fifteen: assert property (
        @(posedge CLK) disable iff (!RESETn) (binary == 4'h1) |-> (twos_comp == 4'hF)
    );

    // If current input equals previous output, current output equals previous input (involution over two cycles).
    check_involution_across_cycles: assert property (
        @(posedge CLK) disable iff (!RESETn) $past(RESETn) && (binary == $past(twos_comp)) |-> (twos_comp == $past(binary))
    );

    // If input is stable across a cycle, output must also be stable.
    check_output_stable_when_input_stable: assert property (
        @(posedge CLK) disable iff (!RESETn) $past(RESETn) && $stable(binary) |-> $stable(twos_comp)
    );
endmodule