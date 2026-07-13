module barrel_shifter_sva (
    // Added clock for SVA sampling
    input logic clk,

    // DUT ports
    input logic [3:0] data,
    input logic [1:0] shift_amount,
    input logic [3:0] result
);
    // Analysis: no reset; pure combinational always @(*); behavior is case-based bit permutation.

    // Result must equal data when shift_amount == 2'b00.
    check_shift00_identity: assert property (
        @(posedge clk) (shift_amount == 2'b00) |-> (result == data)
    );

    // Result must equal {data[3], data[0], data[1], data[2]} when shift_amount == 2'b01.
    check_shift01_permutation: assert property (
        @(posedge clk) (shift_amount == 2'b01) |-> (result == {data[3], data[0], data[1], data[2]})
    );

    // Result must equal {data[2], data[3], data[0], data[1]} when shift_amount == 2'b10.
    check_shift10_permutation: assert property (
        @(posedge clk) (shift_amount == 2'b10) |-> (result == {data[2], data[3], data[0], data[1]})
    );

    // Result must equal {data[1], data[2], data[3], data[0]} when shift_amount == 2'b11.
    check_shift11_permutation: assert property (
        @(posedge clk) (shift_amount == 2'b11) |-> (result == {data[1], data[2], data[3], data[0]})
    );

    // Result must always equal the case-derived permutation for the current shift_amount.
    check_functional_equivalence: assert property (
        @(posedge clk)
            result == (
                (shift_amount == 2'b00) ? data :
                (shift_amount == 2'b01) ? {data[3], data[0], data[1], data[2]} :
                (shift_amount == 2'b10) ? {data[2], data[3], data[0], data[1]} :
                                          {data[1], data[2], data[3], data[0]}
            )
    );

endmodule