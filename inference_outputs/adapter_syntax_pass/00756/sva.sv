module shift_register_sva (
    input logic [3:0] in,
    input logic       shift_dir,
    input logic       clk,
    input logic [3:0] out,
    input logic [3:0] reg1,
    input logic [3:0] reg2,
    input logic [3:0] reg3,
    input logic [3:0] reg4
);

    // reg1 captures in on a shift-left cycle.
    check_reg1_load_left: assert property (
        @(posedge clk) (shift_dir == 1'b0) |=> (reg1 == $past(in))
    );

    // reg2 captures reg1 on a shift-left cycle.
    check_reg2_load_left: assert property (
        @(posedge clk) (shift_dir == 1'b0) |=> (reg2 == $past(reg1))
    );

    // reg3 captures reg2 on a shift-left cycle.
    check_reg3_load_left: assert property (
        @(posedge clk) (shift_dir == 1'b0) |=> (reg3 == $past(reg2))
    );

    // reg4 captures reg3 on a shift-left cycle.
    check_reg4_load_left: assert property (
        @(posedge clk) (shift_dir == 1'b0) |=> (reg4 == $past(reg3))
    );

    // reg4 captures reg3 on a shift-right cycle.
    check_reg4_load_right: assert property (
        @(posedge clk) (shift_dir == 1'b1) |=> (reg4 == $past(reg3))
    );

    // reg3 captures reg2 on a shift-right cycle.
    check_reg3_load_right: assert property (
        @(posedge clk) (shift_dir == 1'b1) |=> (reg3 == $past(reg2))
    );

    // reg2 captures reg1 on a shift-right cycle.
    check_reg2_load_right: assert property (
        @(posedge clk) (shift_dir == 1'b1) |=> (reg2 == $past(reg1))
    );

    // reg1 captures in on a shift-right cycle.
    check_reg1_load_right: assert property (
        @(posedge clk) (shift_dir == 1'b1) |=> (reg1 == $past(in))
    );

    // out is driven by reg4 on the next cycle.
    check_out_follows_reg4: assert property (
        @(posedge clk) 1'b1 |=> (out == $past(reg4))
    );

    // out reflects the previous cycle's shift direction.
    check_out_tracks_shift_direction: assert property (
        @(posedge clk) 1'b1 |=> (out == ($past(shift_dir) ? $past(reg3) : $past(reg1)))
    );

endmodule