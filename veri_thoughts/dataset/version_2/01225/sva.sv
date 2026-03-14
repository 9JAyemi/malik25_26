module barrel_shifter_sva (
    input logic clk,
    input logic [3:0] D,
    input logic [1:0] A,
    input logic [3:0] S
);
    // For A==2'b00, output passes input D.
    check_A00_passthrough: assert property (
        @(posedge clk) (A == 2'b00) |-> (S == D)
    );

    // For A==2'b01, output is {D[0],3'b000}.
    check_A01_shift3_from_D0: assert property (
        @(posedge clk) (A == 2'b01) |-> (S == {D[0], 3'b000})
    );

    // For A==2'b10 or 2'b11, output is all zeros.
    check_Amsb1_forces_zero: assert property (
        @(posedge clk) (A[1] == 1'b1) |-> (S == 4'b0000)
    );

    // When A!=2'b00, lower three bits of S are zero.
    check_lower_bits_zero_when_not_A00: assert property (
        @(posedge clk) (A != 2'b00) |-> (S[2:0] == 3'b000)
    );

    // MSB mapping: A==00 -> D[3], A==01 -> D[0], otherwise 0.
    check_msb_mapping: assert property (
        @(posedge clk) S[3] == ((A == 2'b00) ? D[3] :
                                (A == 2'b01) ? D[0] :
                                1'b0)
    );

    // All-zero input must produce all-zero output.
    check_zero_propagation: assert property (
        @(posedge clk) (D == 4'b0000) |-> (S == 4'b0000)
    );
endmodule