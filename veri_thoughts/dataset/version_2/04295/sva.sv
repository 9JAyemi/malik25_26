module parallel_load_shift_sva (
    input logic        clk,
    input logic [7:0]  data_in,
    input logic [2:0]  shift_amount,
    input logic [7:0]  data_out,
    input logic [7:0]  reg1,
    input logic [7:0]  reg2,
    input logic [7:0]  reg3,
    input logic [7:0]  reg4,
    input logic [7:0]  shifted_reg1,
    input logic [7:0]  shifted_reg2,
    input logic [7:0]  shifted_reg3
);

    // Clock: clk; reset: none; pipeline regs plus combinational shifts.
    // reg1 captures data_in on the next clock.
    check_reg1_captures_data_in: assert property (
        @(posedge clk) 1'b1 |=> (reg1 == $past(data_in))
    );

    // reg2 captures reg1 on the next clock.
    check_reg2_captures_reg1: assert property (
        @(posedge clk) 1'b1 |=> (reg2 == $past(reg1))
    );

    // reg3 captures reg2 on the next clock.
    check_reg3_captures_reg2: assert property (
        @(posedge clk) 1'b1 |=> (reg3 == $past(reg2))
    );

    // reg4 captures reg3 on the next clock.
    check_reg4_captures_reg3: assert property (
        @(posedge clk) 1'b1 |=> (reg4 == $past(reg3))
    );

    // reg4 is a four-cycle delayed version of data_in.
    check_reg4_four_cycle_delay: assert property (
        @(posedge clk) 1'b1 |-> ##4 (reg4 == $past(data_in, 4))
    );

    // shifted_reg1 is reg1 shifted by shift_amount[2].
    check_shifted_reg1_definition: assert property (
        @(posedge clk) (shifted_reg1 == (reg1 >> shift_amount[2]))
    );

    // shifted_reg2 is reg2 shifted by shift_amount[1].
    check_shifted_reg2_definition: assert property (
        @(posedge clk) (shifted_reg2 == (reg2 >> shift_amount[1]))
    );

    // shifted_reg3 is reg3 shifted by shift_amount[0].
    check_shifted_reg3_definition: assert property (
        @(posedge clk) (shifted_reg3 == (reg3 >> shift_amount[0]))
    );

    // data_out equals shifted_reg1 after concatenation truncation.
    check_data_out_equals_shifted_reg1: assert property (
        @(posedge clk) (data_out == shifted_reg1)
    );

    // data_out reflects the prior data_in shifted by current shift_amount[2].
    check_data_out_matches_delayed_input_shift: assert property (
        @(posedge clk) 1'b1 |=> (data_out == ($past(data_in) >> shift_amount[2]))
    );

endmodule