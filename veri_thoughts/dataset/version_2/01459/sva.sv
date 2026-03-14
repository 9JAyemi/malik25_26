module num_2_sva (
    input logic CLK,
    input logic [2:0] in_row,
    input logic [4:0] out_code
);
    // Row 000 maps to 01110.
    map_row_000: assert property (
        @(posedge CLK) disable iff (1'b0) (in_row == 3'b000) |-> (out_code == 5'b01110)
    );

    // Row 001 maps to 10001.
    map_row_001: assert property (
        @(posedge CLK) disable iff (1'b0) (in_row == 3'b001) |-> (out_code == 5'b10001)
    );

    // Row 010 maps to 01000.
    map_row_010: assert property (
        @(posedge CLK) disable iff (1'b0) (in_row == 3'b010) |-> (out_code == 5'b01000)
    );

    // Row 011 maps to 00100.
    map_row_011: assert property (
        @(posedge CLK) disable iff (1'b0) (in_row == 3'b011) |-> (out_code == 5'b00100)
    );

    // Row 100 maps to 00010.
    map_row_100: assert property (
        @(posedge CLK) disable iff (1'b0) (in_row == 3'b100) |-> (out_code == 5'b00010)
    );

    // Row 101 maps to 11111.
    map_row_101: assert property (
        @(posedge CLK) disable iff (1'b0) (in_row == 3'b101) |-> (out_code == 5'b11111)
    );

    // Row 110 maps to 00000 (default).
    map_default_row_110: assert property (
        @(posedge CLK) disable iff (1'b0) (in_row == 3'b110) |-> (out_code == 5'b00000)
    );

    // Row 111 maps to 00000 (default).
    map_default_row_111: assert property (
        @(posedge CLK) disable iff (1'b0) (in_row == 3'b111) |-> (out_code == 5'b00000)
    );

    // out_code is always one of the defined patterns.
    out_code_value_legal_set: assert property (
        @(posedge CLK) disable iff (1'b0) out_code inside {5'b01110,5'b10001,5'b01000,5'b00100,5'b00010,5'b11111,5'b00000}
    );

    // For mapped rows 000..101, out_code is never 00000.
    nonzero_when_row_mapped: assert property (
        @(posedge CLK) disable iff (1'b0) (in_row inside {3'b000,3'b001,3'b010,3'b011,3'b100,3'b101}) |-> (out_code != 5'b00000)
    );
endmodule