module comparator_sva (
    input logic        clk,
    input logic [15:0] A,
    input logic [15:0] B,
    input logic        result
);

    // Result goes high when A is less than or equal to B.
    check_result_when_le: assert property (
        @(posedge clk) ((A <= B) === 1'b1) |-> (result === 1'b1)
    );

    // Result goes low when the comparison is not true.
    check_result_when_not_le: assert property (
        @(posedge clk) ((A <= B) !== 1'b1) |-> (result === 1'b0)
    );

endmodule