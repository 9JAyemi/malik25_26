module barrel_shifter_sva (
    input logic        clk,
    input logic [3:0]  D,
    input logic [1:0]  A,
    input logic [3:0]  S
);

    // Output matches a logical left shift of D by A.
    check_shift_relation: assert property (
        @(posedge clk) S == (D << A)
    );

    // A value of 0 passes D through unchanged.
    check_shift_by_0: assert property (
        @(posedge clk) (A == 2'b00) |-> (S == D)
    );

    // A value of 1 shifts D left by 1 with zero fill.
    check_shift_by_1: assert property (
        @(posedge clk) (A == 2'b01) |-> (S == {D[2:0], 1'b0})
    );

    // A value of 2 shifts D left by 2 with zero fill.
    check_shift_by_2: assert property (
        @(posedge clk) (A == 2'b10) |-> (S == {D[1:0], 2'b00})
    );

    // A value of 3 shifts D left by 3 with zero fill.
    check_shift_by_3: assert property (
        @(posedge clk) (A == 2'b11) |-> (S == {D[0], 3'b000})
    );

endmodule