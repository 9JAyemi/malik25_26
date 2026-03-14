module four_bit_decoder_sva (
    input  logic        CLK,   // Sampling clock for assertions
    input  logic [3:0]  A,
    input  logic [3:0]  B
);
    // B must equal binary-to-Gray conversion: A ^ (A >> 1).
    check_gray_formula: assert property (
        @(posedge CLK) disable iff (1'b0) B == (A ^ (A >> 1))
    );

    // When A==0000, B must be 0000.
    check_map_A_0000: assert property (
        @(posedge CLK) disable iff (1'b0) (A == 4'b0000) |-> (B == 4'b0000)
    );
    // When A==0001, B must be 0001.
    check_map_A_0001: assert property (
        @(posedge CLK) disable iff (1'b0) (A == 4'b0001) |-> (B == 4'b0001)
    );
    // When A==0010, B must be 0011.
    check_map_A_0010: assert property (
        @(posedge CLK) disable iff (1'b0) (A == 4'b0010) |-> (B == 4'b0011)
    );
    // When A==0011, B must be 0010.
    check_map_A_0011: assert property (
        @(posedge CLK) disable iff (1'b0) (A == 4'b0011) |-> (B == 4'b0010)
    );
    // When A==0100, B must be 0110.
    check_map_A_0100: assert property (
        @(posedge CLK) disable iff (1'b0) (A == 4'b0100) |-> (B == 4'b0110)
    );
    // When A==0101, B must be 0111.
    check_map_A_0101: assert property (
        @(posedge CLK) disable iff (1'b0) (A == 4'b0101) |-> (B == 4'b0111)
    );
    // When A==0110, B must be 0101.
    check_map_A_0110: assert property (
        @(posedge CLK) disable iff (1'b0) (A == 4'b0110) |-> (B == 4'b0101)
    );
    // When A==0111, B must be 0100.
    check_map_A_0111: assert property (
        @(posedge CLK) disable iff (1'b0) (A == 4'b0111) |-> (B == 4'b0100)
    );
    // When A==1000, B must be 1100.
    check_map_A_1000: assert property (
        @(posedge CLK) disable iff (1'b0) (A == 4'b1000) |-> (B == 4'b1100)
    );
    // When A==1001, B must be 1101.
    check_map_A_1001: assert property (
        @(posedge CLK) disable iff (1'b0) (A == 4'b1001) |-> (B == 4'b1101)
    );
    // When A==1010, B must be 1111.
    check_map_A_1010: assert property (
        @(posedge CLK) disable iff (1'b0) (A == 4'b1010) |-> (B == 4'b1111)
    );
    // When A==1011, B must be 1110.
    check_map_A_1011: assert property (
        @(posedge CLK) disable iff (1'b0) (A == 4'b1011) |-> (B == 4'b1110)
    );
    // When A==1100, B must be 1010.
    check_map_A_1100: assert property (
        @(posedge CLK) disable iff (1'b0) (A == 4'b1100) |-> (B == 4'b1010)
    );
    // When A==1101, B must be 1011.
    check_map_A_1101: assert property (
        @(posedge CLK) disable iff (1'b0) (A == 4'b1101) |-> (B == 4'b1011)
    );
    // When A==1110, B must be 1001.
    check_map_A_1110: assert property (
        @(posedge CLK) disable iff (1'b0) (A == 4'b1110) |-> (B == 4'b1001)
    );
    // When A==1111, B must be 1000.
    check_map_A_1111: assert property (
        @(posedge CLK) disable iff (1'b0) (A == 4'b1111) |-> (B == 4'b1000)
    );
endmodule