module top_module_sva (
    input logic clk,
    input logic [2:0] in,
    input logic [7:0] O
);

    // Output is always either zero or a single asserted bit.
    check_output_is_onehot0: assert property (
        @(posedge clk) $onehot0(O)
    );

    // Input 000 maps to bit 0.
    check_in_000_maps_to_01: assert property (
        @(posedge clk) (in == 3'b000) |-> (O == 8'b00000001)
    );

    // Input 001 maps to bit 1.
    check_in_001_maps_to_02: assert property (
        @(posedge clk) (in == 3'b001) |-> (O == 8'b00000010)
    );

    // Input 010 produces the default zero output.
    check_in_010_maps_to_00: assert property (
        @(posedge clk) (in == 3'b010) |-> (O == 8'b00000000)
    );

    // Input 011 produces the default zero output.
    check_in_011_maps_to_00: assert property (
        @(posedge clk) (in == 3'b011) |-> (O == 8'b00000000)
    );

    // Input 100 maps to bit 4.
    check_in_100_maps_to_10: assert property (
        @(posedge clk) (in == 3'b100) |-> (O == 8'b00010000)
    );

    // Input 101 maps to bit 5.
    check_in_101_maps_to_20: assert property (
        @(posedge clk) (in == 3'b101) |-> (O == 8'b00100000)
    );

    // Input 110 maps to bit 6.
    check_in_110_maps_to_40: assert property (
        @(posedge clk) (in == 3'b110) |-> (O == 8'b01000000)
    );

    // Input 111 maps to bit 7.
    check_in_111_maps_to_80: assert property (
        @(posedge clk) (in == 3'b111) |-> (O == 8'b10000000)
    );

endmodule