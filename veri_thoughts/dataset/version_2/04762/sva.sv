module mux_4to1_using_2to1_sva (
    input logic       clk,
    input logic [3:0] in,
    input logic [1:0] sel,
    input logic       out
);

    // Combinational DUT sampled on an external formal clock.

    // Output matches the implemented mux function on every sample.
    check_output_matches_implemented_function: assert property (
        @(posedge clk)
        out == (sel[1] ? (sel[0] ? in[2] : in[3]) : (sel[0] ? in[1] : in[0]))
    );

    // When sel[1] is low, the output comes from the lower input pair.
    check_sel_msb_low_selects_lower_pair: assert property (
        @(posedge clk)
        (sel[1] == 1'b0) |-> (out == (sel[0] ? in[1] : in[0]))
    );

    // When sel[1] is high, the output comes from the upper input pair in reversed sel[0] order.
    check_sel_msb_high_selects_upper_pair_reversed: assert property (
        @(posedge clk)
        (sel[1] == 1'b1) |-> (out == (sel[0] ? in[2] : in[3]))
    );

    // Select 00 maps to input bit 0.
    check_sel_00_selects_in0: assert property (
        @(posedge clk)
        (sel == 2'b00) |-> (out == in[0])
    );

    // Select 01 maps to input bit 1.
    check_sel_01_selects_in1: assert property (
        @(posedge clk)
        (sel == 2'b01) |-> (out == in[1])
    );

    // Select 10 maps to input bit 3.
    check_sel_10_selects_in3: assert property (
        @(posedge clk)
        (sel == 2'b10) |-> (out == in[3])
    );

    // Select 11 maps to input bit 2.
    check_sel_11_selects_in2: assert property (
        @(posedge clk)
        (sel == 2'b11) |-> (out == in[2])
    );

    // If sel and the selected input stay stable, the output stays stable.
    check_output_stable_when_selected_input_stable: assert property (
        @(posedge clk)
        $stable(sel) &&
        (((sel == 2'b00) && $stable(in[0])) ||
         ((sel == 2'b01) && $stable(in[1])) ||
         ((sel == 2'b10) && $stable(in[3])) ||
         ((sel == 2'b11) && $stable(in[2])))
        |-> $stable(out)
    );

    // With a stable select, any output change must track the selected input.
    check_output_change_requires_selected_input_change: assert property (
        @(posedge clk)
        $stable(sel) && $changed(out)
        |-> (((sel == 2'b00) && $changed(in[0])) ||
             ((sel == 2'b01) && $changed(in[1])) ||
             ((sel == 2'b10) && $changed(in[3])) ||
             ((sel == 2'b11) && $changed(in[2])))
    );

endmodule