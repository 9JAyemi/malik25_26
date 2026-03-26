module binary_counter_sva (
    input logic       clk,
    input logic       reset,
    input logic       enable,
    input logic [2:0] count,
    input logic [2:0] shift_reg,
    input logic [1:0] flip_flop
);

    // Reset clears shift_reg.
    check_reset_clears_shift_reg: assert property (
        @(posedge clk) reset |=> (shift_reg == 3'b000)
    );

    // Reset clears flip_flop.
    check_reset_clears_flip_flop: assert property (
        @(posedge clk) reset |=> (flip_flop == 2'b00)
    );

    // Reset clears count.
    check_reset_clears_count: assert property (
        @(posedge clk) reset |=> (count == 3'b000)
    );

    // Enable updates flip_flop from its previous LSB and shift_reg MSB.
    check_enable_updates_flip_flop: assert property (
        @(posedge clk) disable iff (reset)
        enable |=> (flip_flop == { $past(flip_flop[0]), $past(shift_reg[2]) })
    );

    // Enable updates shift_reg from previous flip_flop[1] and shift_reg[2:1].
    check_enable_updates_shift_reg: assert property (
        @(posedge clk) disable iff (reset)
        enable |=> (shift_reg == { $past(flip_flop[1]), $past(shift_reg[2:1]) })
    );

    // Enable updates count with the previous shift_reg value.
    check_enable_updates_count: assert property (
        @(posedge clk) disable iff (reset)
        enable |=> (count == $past(shift_reg))
    );

    // Without enable, flip_flop holds its value.
    check_idle_holds_flip_flop: assert property (
        @(posedge clk) disable iff (reset)
        !enable |=> (flip_flop == $past(flip_flop))
    );

    // Without enable, shift_reg holds its value.
    check_idle_holds_shift_reg: assert property (
        @(posedge clk) disable iff (reset)
        !enable |=> (shift_reg == $past(shift_reg))
    );

    // Without enable, count holds its value.
    check_idle_holds_count: assert property (
        @(posedge clk) disable iff (reset)
        !enable |=> (count == $past(count))
    );

endmodule