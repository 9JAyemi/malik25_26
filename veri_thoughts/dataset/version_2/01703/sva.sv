module mux_multiply_sva (
    input logic CLK,
    input logic [3:0] in_0,
    input logic [3:0] in_1,
    input logic sel,
    input logic [7:0] out
);
    // Out equals square of the selected input.
    check_out_is_square: assert property (
        @(posedge CLK) out == ((sel ? in_1 : in_0) * (sel ? in_1 : in_0))
    );

    // When sel=0, out equals in_0 squared.
    check_sel0_square: assert property (
        @(posedge CLK) (sel == 1'b0) |-> (out == (in_0 * in_0))
    );

    // When sel=1, out equals in_1 squared.
    check_sel1_square: assert property (
        @(posedge CLK) (sel == 1'b1) |-> (out == (in_1 * in_1))
    );

    // Out is always within 0..225 for a 4-bit square.
    check_out_range: assert property (
        @(posedge CLK) out <= 8'd225
    );

    // If sel=0 and in_0==0 then out==0.
    check_zero_case_sel0: assert property (
        @(posedge CLK) (sel == 1'b0 && (in_0 == 4'd0)) |-> (out == 8'd0)
    );

    // If sel=1 and in_1==0 then out==0.
    check_zero_case_sel1: assert property (
        @(posedge CLK) (sel == 1'b1 && (in_1 == 4'd0)) |-> (out == 8'd0)
    );

    // LSB of out equals LSB of the selected input (square preserves parity).
    check_parity_lsb: assert property (
        @(posedge CLK) out[0] == (sel ? in_1[0] : in_0[0])
    );

    // If in_0, in_1, and sel are stable, out is stable.
    check_out_stable_when_inputs_stable: assert property (
        @(posedge CLK) ($stable(in_0) && $stable(in_1) && $stable(sel)) |-> $stable(out)
    );

    // If in_0==in_1, toggling sel does not change out.
    check_sel_change_no_effect_when_inputs_equal: assert property (
        @(posedge CLK) ((in_0 == in_1) && $changed(sel)) |-> $stable(out)
    );

    // If out==0, the selected input must be 0.
    check_zero_output_implies_zero_input: assert property (
        @(posedge CLK) (out == 8'd0) |-> ((sel ? in_1 : in_0) == 4'd0)
    );

    // If out==1, the selected input must be 1.
    check_one_output_implies_one_input: assert property (
        @(posedge CLK) (out == 8'd1) |-> ((sel ? in_1 : in_0) == 4'd1)
    );

    // When sel=0, changes on in_1 alone do not affect out.
    check_in1_no_effect_when_sel0: assert property (
        @(posedge CLK) (sel == 1'b0 && $changed(in_1) && $stable(in_0) && $stable(sel)) |-> $stable(out)
    );

    // When sel=1, changes on in_0 alone do not affect out.
    check_in0_no_effect_when_sel1: assert property (
        @(posedge CLK) (sel == 1'b1 && $changed(in_0) && $stable(in_1) && $stable(sel)) |-> $stable(out)
    );
endmodule