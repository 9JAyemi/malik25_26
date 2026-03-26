module binary_converter_sva (
    input logic        clk,
    input logic [3:0]  D,
    input logic [2:0]  Q
);

    // Q must follow the RTL's full combinational mapping.
    check_full_mapping: assert property (
        @(posedge clk)
        Q == ((D[3] == 1'b0) ? D[2:0] : {1'b0, (D[3:2] - 2'b11)})
    );

    // Inputs 0 through 7 pass D[2:0] directly to Q.
    check_low_range_passthrough: assert property (
        @(posedge clk)
        (D[3] == 1'b0) |-> (Q == D[2:0])
    );

    // Inputs 8 through 15 use the subtract result, zero-extended to 3 bits.
    check_high_range_conversion: assert property (
        @(posedge clk)
        (D[3] == 1'b1) |-> (Q == {1'b0, (D[3:2] - 2'b11)})
    );

    // For inputs 8 through 11, Q must be 3.
    check_range_8_to_11_value: assert property (
        @(posedge clk)
        (D[3:2] == 2'b10) |-> (Q == 3'b011)
    );

    // For inputs 12 through 15, Q must be 0.
    check_range_12_to_15_value: assert property (
        @(posedge clk)
        (D[3:2] == 2'b11) |-> (Q == 3'b000)
    );

    // The upper bit of Q is cleared whenever the subtract path is selected.
    check_high_range_msb_zero: assert property (
        @(posedge clk)
        (D[3] == 1'b1) |-> (Q[2] == 1'b0)
    );

endmodule