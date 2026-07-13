module top_module_sva (
    input logic clk,
    input logic [7:0] d,
    input logic select,
    input logic out
);

    // When select==0, out is the reduction AND of d from the previous cycle.
    check_out_is_and_when_select0: assert property (
        @(posedge clk) ($past(1'b1) && (select == 1'b0)) |-> (out == (&$past(d)))
    );

    // When select==1, out is the reduction OR of d from the previous cycle.
    check_out_is_or_when_select1: assert property (
        @(posedge clk) ($past(1'b1) && (select == 1'b1)) |-> (out == (|$past(d)))
    );

    // If previous-cycle input was all zeros, out must be 0 regardless of select.
    check_zero_input_forces_zero: assert property (
        @(posedge clk) ($past(1'b1) && ($past(d) == 8'h00)) |-> (out == 1'b0)
    );

    // If previous-cycle input was all ones, out must be 1 regardless of select.
    check_ones_input_forces_one: assert property (
        @(posedge clk) ($past(1'b1) && ($past(d) == 8'hFF)) |-> (out == 1'b1)
    );

    // If select stays 0 and prior-cycle d equals d from two cycles ago, out is stable.
    check_stable_output_select0: assert property (
        @(posedge clk) ($past(1'b1,2) && (select == 1'b0) && ($past(select) == 1'b0) && ($past(d) == $past(d,2))) |-> (out == $past(out))
    );

    // If select stays 1 and prior-cycle d equals d from two cycles ago, out is stable.
    check_stable_output_select1: assert property (
        @(posedge clk) ($past(1'b1,2) && (select == 1'b1) && ($past(select) == 1'b1) && ($past(d) == $past(d,2))) |-> (out == $past(out))
    );

    // On a rising edge of select, out equals the OR-reduction of prior-cycle d.
    check_out_on_select_rise: assert property (
        @(posedge clk) ($past(1'b1) && $rose(select)) |-> (out == (|$past(d)))
    );

    // On a falling edge of select, out equals the AND-reduction of prior-cycle d.
    check_out_on_select_fall: assert property (
        @(posedge clk) ($past(1'b1) && $fell(select)) |-> (out == (&$past(d)))
    );

endmodule