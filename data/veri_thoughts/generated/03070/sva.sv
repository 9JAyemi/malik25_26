module booth_encoder_5_sva (
    input logic       clk,
    input logic [2:0] B_in,
    input logic [2:0] A_out
);

    // Combinational DUT with no RTL reset, sampled on an external clock.

    // Zero input produces the zero code.
    check_000_maps_to_000: assert property (
        @(posedge clk) (B_in == 3'b000) |-> (A_out == 3'b000)
    );

    // Input 001 produces code 001.
    check_001_maps_to_001: assert property (
        @(posedge clk) (B_in == 3'b001) |-> (A_out == 3'b001)
    );

    // Input 010 produces code 001.
    check_010_maps_to_001: assert property (
        @(posedge clk) (B_in == 3'b010) |-> (A_out == 3'b001)
    );

    // Input 011 produces code 010.
    check_011_maps_to_010: assert property (
        @(posedge clk) (B_in == 3'b011) |-> (A_out == 3'b010)
    );

    // Input 100 produces code 001.
    check_100_maps_to_001: assert property (
        @(posedge clk) (B_in == 3'b100) |-> (A_out == 3'b001)
    );

    // Input 101 produces code 011.
    check_101_maps_to_011: assert property (
        @(posedge clk) (B_in == 3'b101) |-> (A_out == 3'b011)
    );

    // Input 110 produces code 010.
    check_110_maps_to_010: assert property (
        @(posedge clk) (B_in == 3'b110) |-> (A_out == 3'b010)
    );

    // Input 111 produces code 001.
    check_111_maps_to_001: assert property (
        @(posedge clk) (B_in == 3'b111) |-> (A_out == 3'b001)
    );

    // The implemented encoder never drives the output MSB high.
    check_output_msb_is_zero: assert property (
        @(posedge clk) (A_out[2] == 1'b0)
    );

endmodule