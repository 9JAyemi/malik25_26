module top_module_sva (
    input logic clk,
    input logic reset,
    input logic [7:0] d,
    input logic [1:0] select,
    input logic [11:0] q,
    // Internal design signals
    input logic [7:0] reg_out,
    input logic [3:0] counter_out,
    input logic [7:0] selected_input,
    input logic [11:0] added_output
);

    ///// Reset behavior /////
    // During reset, reg_out is 0x34.
    check_reg_out_reset_value: assert property (
        @(posedge clk) reset |-> (reg_out == 8'h34)
    );
    // During reset, counter_out is 0.
    check_counter_reset_value: assert property (
        @(posedge clk) reset |-> (counter_out == 4'h0)
    );

    ///// Register behavior /////
    // When not in reset and previous cycle not in reset, reg_out captures previous d.
    check_reg_out_loads_d: assert property (
        @(posedge clk) disable iff (reset) (!$past(reset)) |-> (reg_out == $past(d))
    );

    ///// Counter behavior /////
    // When not in reset and previous cycle not in reset, counter_out increments by 1 (mod 16).
    check_counter_increments: assert property (
        @(posedge clk) disable iff (reset) (!$past(reset)) |-> (counter_out == ($past(counter_out) + 4'd1))
    );

    ///// Selection logic /////
    // When select == 2'b00, selected_input equals reg_out.
    check_select00_uses_reg_out: assert property (
        @(posedge clk) disable iff (reset) (select == 2'b00) |-> (selected_input == reg_out)
    );
    // When select == 2'b01, selected_input equals zero-extended counter_out.
    check_select01_uses_counter_zero_ext: assert property (
        @(posedge clk) disable iff (reset) (select == 2'b01) |-> ((selected_input[3:0] == counter_out) && (selected_input[7:4] == 4'h0))
    );
    // When select is neither 00 nor 01, selected_input is zero.
    check_select_other_zero: assert property (
        @(posedge clk) disable iff (reset) ((select != 2'b00) && (select != 2'b01)) |-> (selected_input == 8'h00)
    );

    ///// Adder and output /////
    // added_output equals zero-extended sum of selected_input and reg_out.
    check_added_output_sum_definition: assert property (
        @(posedge clk) disable iff (reset) (added_output == ({4'b0, selected_input} + {4'b0, reg_out}))
    );
    // q equals added_output.
    check_q_ties_to_added_output: assert property (
        @(posedge clk) disable iff (reset) (q == added_output)
    );
    // When select == 2'b00, added_output equals reg_out + reg_out (zero-extended).
    check_select00_sum_double_reg_out: assert property (
        @(posedge clk) disable iff (reset) (select == 2'b00) |-> (added_output == ({4'b0, reg_out} + {4'b0, reg_out}))
    );

endmodule