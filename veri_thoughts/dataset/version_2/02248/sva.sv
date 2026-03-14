module decoder_4to16_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [15:0] Y
);
    // Output equals one-hot value of 1 shifted by A.
    check_decode_equivalence: assert property (
        @(posedge clk) Y == (16'h0001 << A)
    );

    // Exactly one output bit is HIGH.
    check_onehot_output: assert property (
        @(posedge clk) $onehot(Y)
    );

    // Output is never all zero for 4-bit binary A.
    check_nonzero_output: assert property (
        @(posedge clk) Y != 16'h0000
    );

    // When MSB of A is 0, upper half of Y must be zero.
    check_upper_zero_when_msb0: assert property (
        @(posedge clk) (A[3] == 1'b0) |-> (Y[15:8] == 8'h00)
    );

    // When MSB of A is 1, lower half of Y must be zero.
    check_lower_zero_when_msb1: assert property (
        @(posedge clk) (A[3] == 1'b1) |-> (Y[7:0] == 8'h00)
    );

    // When A[3:2]==00, only Y[3:0] may be nonzero.
    check_quarter00_zero_upper12: assert property (
        @(posedge clk) (A[3:2] == 2'b00) |-> (Y[15:4] == 12'h000)
    );

    // When A[3:2]==01, only Y[7:4] may be nonzero.
    check_quarter01_zero_elsewhere: assert property (
        @(posedge clk) (A[3:2] == 2'b01) |-> (Y[15:8] == 8'h00 && Y[3:0] == 4'h0)
    );

    // When A[3:2]==10, only Y[11:8] may be nonzero.
    check_quarter10_zero_elsewhere: assert property (
        @(posedge clk) (A[3:2] == 2'b10) |-> (Y[15:12] == 4'h0 && Y[7:0] == 8'h00)
    );

    // When A[3:2]==11, only Y[15:12] may be nonzero.
    check_quarter11_zero_lower12: assert property (
        @(posedge clk) (A[3:2] == 2'b11) |-> (Y[11:0] == 12'h000)
    );

    // Corner case: A==0 decodes to Y==0x0001.
    check_decode_A0: assert property (
        @(posedge clk) (A == 4'd0) |-> (Y == 16'h0001)
    );
endmodule