module barrel_shifter_sva (
    input logic clk,
    input logic [3:0] data,
    input logic [1:0] shift_amount,
    input logic [3:0] result
);

// No reset in RTL; assertions are always active.

    // Shift amount 00 passes data through unchanged.
    check_shift_00_passthrough: assert property (
        @(posedge clk) (shift_amount == 2'b00) |-> (result == data)
    );

// Shift amount 01 shifts left by 1 and inserts 0 in bit 0.
    check_shift_01_left1: assert property (
        @(posedge clk) (shift_amount == 2'b01) |-> (result == {data[2:0], 1'b0})
    );

// Shift amount 10 shifts left by 2 and inserts 00 in bits [1:0].
    check_shift_10_left2: assert property (
        @(posedge clk) (shift_amount == 2'b10) |-> (result == {data[1:0], 2'b00})
    );

// Shift amount 11 shifts left by 3 and inserts 000 in bits [2:0].
    check_shift_11_left3: assert property (
        @(posedge clk) (shift_amount == 2'b11) |-> (result == {data[0], 3'b000})
    );

// Result always matches the selected shift function.
    check_functional_equivalence: assert property (
        @(posedge clk)
            result == ((shift_amount == 2'b00) ? data :
                       (shift_amount == 2'b01) ? {data[2:0], 1'b0} :
                       (shift_amount == 2'b10) ? {data[1:0], 2'b00} :
                                                  {data[0], 3'b000})
    );

endmodule
