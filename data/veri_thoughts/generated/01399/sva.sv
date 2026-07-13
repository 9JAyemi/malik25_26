module multiplexer32to16_sva (
    input logic CLK,
    input logic [31:0] out,
    input logic [31:0] in1,
    input logic [31:0] in2,
    input logic control
);
    // Vector mux behavior: out equals control ? in2 : in1.
    check_mux_vector_function: assert property (
        @(posedge CLK) out == (control ? in2 : in1)
    );

    // When control is 0, out equals in1.
    check_out_eq_in1_when_c0: assert property (
        @(posedge CLK) (control == 1'b0) |-> (out == in1)
    );

    // When control is 1, out equals in2.
    check_out_eq_in2_when_c1: assert property (
        @(posedge CLK) (control == 1'b1) |-> (out == in2)
    );

    // Equal inputs produce that value regardless of control.
    check_equal_inputs_dont_care_select: assert property (
        @(posedge CLK) (in1 == in2) |-> (out == in1)
    );

    // Mask-form equivalence: out == (~sel & in1) | (sel & in2).
    check_mask_equivalence: assert property (
        @(posedge CLK) out == ((~({32{control}}) & in1) | (({32{control}}) & in2))
    );

    // On 0->1 control transition, out equals in2 at that sample.
    check_out_after_rose_control: assert property (
        @(posedge CLK) $rose(control) |-> (out == in2)
    );

    // On 1->0 control transition, out equals in1 at that sample.
    check_out_after_fell_control: assert property (
        @(posedge CLK) $fell(control) |-> (out == in1)
    );

    // With control=0 and both control and in1 stable, out is stable.
    check_stability_c0: assert property (
        @(posedge CLK) (control == 1'b0 && $stable(control) && $stable(in1)) |-> $stable(out)
    );

    // With control=1 and both control and in2 stable, out is stable.
    check_stability_c1: assert property (
        @(posedge CLK) (control == 1'b1 && $stable(control) && $stable(in2)) |-> $stable(out)
    );
endmodule