module mux_4to1_enable_sva (
    input logic clk,
    input logic [3:0] in0,
    input logic [3:0] in1,
    input logic [3:0] in2,
    input logic [3:0] in3,
    input logic [1:0] sel,
    input logic en,
    input logic [3:0] out
);

    // Output must match the complete enable-controlled 4:1 mux function.
    check_full_mux_function: assert property (
        @(posedge clk)
        out == ((en == 1'b1) ?
                ((sel == 2'b00) ? in0 :
                 (sel == 2'b01) ? in1 :
                 (sel == 2'b10) ? in2 : in3) :
                4'b0000)
    );

    // Output must be zero whenever the mux is disabled.
    check_output_zero_when_disabled: assert property (
        @(posedge clk)
        (en == 1'b0) |-> (out == 4'b0000)
    );

    // When enabled with sel=00, output must equal in0.
    check_select_in0_when_enabled: assert property (
        @(posedge clk)
        ((en == 1'b1) && (sel == 2'b00)) |-> (out == in0)
    );

    // When enabled with sel=01, output must equal in1.
    check_select_in1_when_enabled: assert property (
        @(posedge clk)
        ((en == 1'b1) && (sel == 2'b01)) |-> (out == in1)
    );

    // When enabled with sel=10, output must equal in2.
    check_select_in2_when_enabled: assert property (
        @(posedge clk)
        ((en == 1'b1) && (sel == 2'b10)) |-> (out == in2)
    );

    // When enabled with sel=11, output must equal in3.
    check_select_in3_when_enabled: assert property (
        @(posedge clk)
        ((en == 1'b1) && (sel == 2'b11)) |-> (out == in3)
    );

    // With sel=00, changes on unselected inputs must not change the output.
    check_unselected_inputs_do_not_affect_out_sel0: assert property (
        @(posedge clk)
        ((en == 1'b1) && $stable(en) &&
         (sel == 2'b00) && $stable(sel) && $stable(in0) &&
         ($changed(in1) || $changed(in2) || $changed(in3)))
        |-> $stable(out)
    );

    // With sel=01, changes on unselected inputs must not change the output.
    check_unselected_inputs_do_not_affect_out_sel1: assert property (
        @(posedge clk)
        ((en == 1'b1) && $stable(en) &&
         (sel == 2'b01) && $stable(sel) && $stable(in1) &&
         ($changed(in0) || $changed(in2) || $changed(in3)))
        |-> $stable(out)
    );

    // With sel=10, changes on unselected inputs must not change the output.
    check_unselected_inputs_do_not_affect_out_sel2: assert property (
        @(posedge clk)
        ((en == 1'b1) && $stable(en) &&
         (sel == 2'b10) && $stable(sel) && $stable(in2) &&
         ($changed(in0) || $changed(in1) || $changed(in3)))
        |-> $stable(out)
    );

    // With sel=11, changes on unselected inputs must not change the output.
    check_unselected_inputs_do_not_affect_out_sel3: assert property (
        @(posedge clk)
        ((en == 1'b1) && $stable(en) &&
         (sel == 2'b11) && $stable(sel) && $stable(in3) &&
         ($changed(in0) || $changed(in1) || $changed(in2)))
        |-> $stable(out)
    );

    // While disabled, input or select changes must not change the zero output.
    check_disabled_input_changes_do_not_affect_out: assert property (
        @(posedge clk)
        ((en == 1'b0) && $stable(en) &&
         ($changed(in0) || $changed(in1) || $changed(in2) || $changed(in3) || $changed(sel)))
        |-> $stable(out)
    );

endmodule