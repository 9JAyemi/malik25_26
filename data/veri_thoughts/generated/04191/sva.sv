module barrel_shifter_sva (
    input logic clk,
    input logic [3:0] data,
    input logic [1:0] shift,
    input logic shift_right,
    input logic shift_left,
    input logic rotate_right,
    input logic rotate_left,
    input logic [3:0] result
);

    // When only shift_right is asserted, result matches the 0001 case mapping.
    check_shift_right_case: assert property (
        @(posedge clk)
        ({rotate_left, rotate_right, shift_left, shift_right} == 4'b0001)
        |-> (result == {data[2:0], data[3]})
    );

    // When only shift_left is asserted, result matches the 0010 case mapping.
    check_shift_left_case: assert property (
        @(posedge clk)
        ({rotate_left, rotate_right, shift_left, shift_right} == 4'b0010)
        |-> (result == {data[1:0], data[3:2]})
    );

    // When only rotate_right is asserted, result matches the 0100 case mapping.
    check_rotate_right_case: assert property (
        @(posedge clk)
        ({rotate_left, rotate_right, shift_left, shift_right} == 4'b0100)
        |-> (result == {data[0], data[3:1]})
    );

    // When only rotate_left is asserted, result matches the 1000 case mapping.
    check_rotate_left_case: assert property (
        @(posedge clk)
        ({rotate_left, rotate_right, shift_left, shift_right} == 4'b1000)
        |-> (result == {data[3], data[2:0]})
    );

    // Any control pattern not explicitly decoded passes data through unchanged.
    check_default_passthrough: assert property (
        @(posedge clk)
        (({rotate_left, rotate_right, shift_left, shift_right} != 4'b0001) &&
         ({rotate_left, rotate_right, shift_left, shift_right} != 4'b0010) &&
         ({rotate_left, rotate_right, shift_left, shift_right} != 4'b0100) &&
         ({rotate_left, rotate_right, shift_left, shift_right} != 4'b1000))
        |-> (result == data)
    );

    // Changing shift alone does not change result because shift is unused.
    check_shift_input_unused: assert property (
        @(posedge clk)
        !$initstate &&
        $changed(shift) &&
        $stable(data) &&
        $stable({rotate_left, rotate_right, shift_left, shift_right})
        |-> $stable(result)
    );

endmodule