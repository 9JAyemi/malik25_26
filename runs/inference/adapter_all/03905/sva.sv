module shift_register_sva (
    input logic clk,
    input logic [7:0] data,
    input logic [7:0] shifted_data
);

    // shifted_data[0] captures data[7] from the previous clock.
    check_shifted_bit0_captures_data7: assert property (
        @(posedge clk) 1'b1 |=> (shifted_data[0] == $past(data[7]))
    );

    // shifted_data[1] shifts in the previous shifted_data[0].
    check_shifted_bit1_shifts_from_bit0: assert property (
        @(posedge clk) 1'b1 |=> (shifted_data[1] == $past(shifted_data[0]))
    );

    // shifted_data[2] shifts in the previous shifted_data[1].
    check_shifted_bit2_shifts_from_bit1: assert property (
        @(posedge clk) 1'b1 |=> (shifted_data[2] == $past(shifted_data[1]))
    );

    // shifted_data[3] shifts in the previous shifted_data[2].
    check_shifted_bit3_shifts_from_bit2: assert property (
        @(posedge clk) 1'b1 |=> (shifted_data[3] == $past(shifted_data[2]))
    );

    // shifted_data[4] shifts in the previous shifted_data[3].
    check_shifted_bit4_shifts_from_bit3: assert property (
        @(posedge clk) 1'b1 |=> (shifted_data[4] == $past(shifted_data[3]))
    );

    // shifted_data[5] shifts in the previous shifted_data[4].
    check_shifted_bit5_shifts_from_bit4: assert property (
        @(posedge clk) 1'b1 |=> (shifted_data[5] == $past(shifted_data[4]))
    );

    // shifted_data[6] shifts in the previous shifted_data[5].
    check_shifted_bit6_shifts_from_bit5: assert property (
        @(posedge clk) 1'b1 |=> (shifted_data[6] == $past(shifted_data[5]))
    );

    // shifted_data[7] shifts in the previous shifted_data[6].
    check_shifted_bit7_shifts_from_bit6: assert property (
        @(posedge clk) 1'b1 |=> (shifted_data[7] == $past(shifted_data[6]))
    );

endmodule