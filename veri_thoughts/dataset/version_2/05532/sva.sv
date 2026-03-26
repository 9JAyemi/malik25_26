module shift_register_assertions (
    input logic       clk,
    input logic       reset,
    input logic       load,
    input logic [3:0] data_in,
    input logic [3:0] data_out,
    input logic [3:0] reg1,
    input logic [3:0] reg2,
    input logic [3:0] reg3,
    input logic [3:0] reg4
);

    // Reset clears all stages and the output.
    check_reset_clears_state: assert property (
        @(posedge clk)
        reset |=> (reg1 == 4'b0000) &&
                  (reg2 == 4'b0000) &&
                  (reg3 == 4'b0000) &&
                  (reg4 == 4'b0000) &&
                  (data_out == 4'b0000)
    );

    // A load captures data_in into reg1.
    check_load_captures_reg1: assert property (
        @(posedge clk) disable iff (reset)
        load |=> (reg1 == $past(data_in))
    );

    // Without load, reg1 holds its previous value.
    check_reg1_holds_without_load: assert property (
        @(posedge clk) disable iff (reset)
        !load |=> (reg1 == $past(reg1))
    );

    // reg2 shifts in the previous reg1 value each cycle.
    check_reg2_shifts_reg1: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (reg2 == $past(reg1))
    );

    // reg3 shifts in the previous reg2 value each cycle.
    check_reg3_shifts_reg2: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (reg3 == $past(reg2))
    );

    // reg4 shifts in the previous reg3 value each cycle.
    check_reg4_shifts_reg3: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (reg4 == $past(reg3))
    );

    // data_out always reflects reg4.
    check_data_out_matches_reg4: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |-> (data_out == reg4)
    );

    // A loaded input value appears at the output four cycles later.
    check_load_reaches_output_after_four_cycles: assert property (
        @(posedge clk) disable iff (reset)
        load |-> ##4 (data_out == $past(data_in, 4))
    );

endmodule