module mux2to1_sva (
    input logic [3:0] in0,
    input logic [3:0] in1,
    input logic       sel,
    input logic [3:0] out
);
    // Out equals selected input on any relevant signal edge.
    check_mux_function_vector: assert property (
        @(posedge sel or negedge sel
          or posedge in0[0] or negedge in0[0]
          or posedge in0[1] or negedge in0[1]
          or posedge in0[2] or negedge in0[2]
          or posedge in0[3] or negedge in0[3]
          or posedge in1[0] or negedge in1[0]
          or posedge in1[1] or negedge in1[1]
          or posedge in1[2] or negedge in1[2]
          or posedge in1[3] or negedge in1[3]
          or posedge out[0] or negedge out[0]
          or posedge out[1] or negedge out[1]
          or posedge out[2] or negedge out[2]
          or posedge out[3] or negedge out[3]
        ) out == (sel ? in1 : in0)
    );

    // On sel rising edge, output follows in1.
    check_out_matches_in1_on_sel_rise: assert property (
        @(posedge sel) out == in1
    );

    // On sel falling edge, output follows in0.
    check_out_matches_in0_on_sel_fall: assert property (
        @(negedge sel) out == in0
    );

    // If inputs are equal, output equals that common value.
    check_equal_inputs_force_out: assert property (
        @(posedge sel or negedge sel
          or posedge in0[0] or negedge in0[0]
          or posedge in0[1] or negedge in0[1]
          or posedge in0[2] or negedge in0[2]
          or posedge in0[3] or negedge in0[3]
          or posedge in1[0] or negedge in1[0]
          or posedge in1[1] or negedge in1[1]
          or posedge in1[2] or negedge in1[2]
          or posedge in1[3] or negedge in1[3]
          or posedge out[0] or negedge out[0]
          or posedge out[1] or negedge out[1]
          or posedge out[2] or negedge out[2]
          or posedge out[3] or negedge out[3]
        ) (in0 == in1) |-> (out == in0)
    );

    // Output must equal either in0 or in1 at all checked edges.
    check_out_equals_one_of_inputs: assert property (
        @(posedge sel or negedge sel
          or posedge in0[0] or negedge in0[0]
          or posedge in0[1] or negedge in0[1]
          or posedge in0[2] or negedge in0[2]
          or posedge in0[3] or negedge in0[3]
          or posedge in1[0] or negedge in1[0]
          or posedge in1[1] or negedge in1[1]
          or posedge in1[2] or negedge in1[2]
          or posedge in1[3] or negedge in1[3]
          or posedge out[0] or negedge out[0]
          or posedge out[1] or negedge out[1]
          or posedge out[2] or negedge out[2]
          or posedge out[3] or negedge out[3]
        ) (out == in0) || (out == in1)
    );

    // Output can only change if sel or one of the inputs changed.
    check_out_changes_only_on_input_change: assert property (
        @(posedge sel or negedge sel
          or posedge in0[0] or negedge in0[0]
          or posedge in0[1] or negedge in0[1]
          or posedge in0[2] or negedge in0[2]
          or posedge in0[3] or negedge in0[3]
          or posedge in1[0] or negedge in1[0]
          or posedge in1[1] or negedge in1[1]
          or posedge in1[2] or negedge in1[2]
          or posedge in1[3] or negedge in1[3]
          or posedge out[0] or negedge out[0]
          or posedge out[1] or negedge out[1]
          or posedge out[2] or negedge out[2]
          or posedge out[3] or negedge out[3]
        ) $changed(out) |-> ($changed(sel) || $changed(in0) || $changed(in1))
    );
endmodule