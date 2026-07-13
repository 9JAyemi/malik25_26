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

    // reg1 captures input on a right shift.
    check_reg1_captures_input_right: assert property (
        @(posedge clk) (shift_dir == 1'b0) |=> (reg1 == $past(in))
    );

    // reg2 captures reg1 on a right shift.
    check_reg2_captures_reg1_right: assert property (
        @(posedge clk) (shift_dir == 1'b0) |=> (reg2 == $past(reg1))
    );

    // reg3 captures reg2 on a right shift.
    check_reg3_captures_reg2_right: assert property (
        @(posedge clk) (shift_dir == 1'b0) |=> (reg3 == $past(reg2))
    );

    // reg4 captures reg3 on a right shift.
    check_reg4_captures_reg3_right: assert property (
        @(posedge clk) (shift_dir == 1'b0) |=> (reg4 == $past(reg3))
    );

    // reg4 captures input on a left shift.
    check_reg4_captures_input_left: assert property (
        @(posedge clk) (shift_dir == 1'b1) |=> (reg4 == $past(in))
    );

    // reg3 captures reg4 on a left shift.
    check_reg3_captures_reg4_left: assert property (
        @(posedge clk) (shift_dir == 1'b1) |=> (reg3 == $past(reg4))
    );

    // reg2 captures reg3 on a left shift.
    check_reg2_captures_reg3_left: assert property (
        @(posedge clk) (shift_dir == 1'b1) |=> (reg2 == $past(reg3))
    );

    // reg1 captures reg2 on a left shift.
    check_reg1_captures_reg2_left: assert property (
        @(posedge clk) (shift_dir == 1'b1) |=> (reg1 == $past(reg2))
    );

    // out reflects reg4 on any clock edge.
    check_out_matches_reg4: assert property (
        @(posedge clk) (out == reg4)
    );

endmodule