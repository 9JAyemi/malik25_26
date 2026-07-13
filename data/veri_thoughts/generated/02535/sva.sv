module mux4to1_sva (
    input logic clk,
    input logic [1:0] sel,
    input logic [3:0] in0,
    input logic [3:0] in1,
    input logic [3:0] in2,
    input logic [3:0] in3,
    input logic [3:0] out
);
    // When sel == 2'b00, out equals in0.
    check_mux_sel_00: assert property (
        @(posedge clk) (sel == 2'b00) |-> (out == in0)
    );

    // When sel == 2'b01, out equals in1.
    check_mux_sel_01: assert property (
        @(posedge clk) (sel == 2'b01) |-> (out == in1)
    );

    // When sel == 2'b10, out equals in2.
    check_mux_sel_10: assert property (
        @(posedge clk) (sel == 2'b10) |-> (out == in2)
    );

    // When sel == 2'b11, out equals in3.
    check_mux_sel_11: assert property (
        @(posedge clk) (sel == 2'b11) |-> (out == in3)
    );

    // Out equals the 4:1 mux function of sel and inputs.
    check_mux_function: assert property (
        @(posedge clk) out == ((sel == 2'b00) ? in0 :
                               (sel == 2'b01) ? in1 :
                               (sel == 2'b10) ? in2 : in3)
    );

    // Out does not change when sel and all inputs remain stable.
    check_stability_when_inputs_stable: assert property (
        @(posedge clk) $stable({sel, in0, in1, in2, in3}) |-> $stable(out)
    );

    // If only sel changes (inputs stable), out updates to the newly selected input.
    check_out_updates_on_sel_change: assert property (
        @(posedge clk) (!$stable(sel) && $stable({in0, in1, in2, in3})) |->
                       (out == ((sel == 2'b00) ? in0 :
                                (sel == 2'b01) ? in1 :
                                (sel == 2'b10) ? in2 : in3))
    );
endmodule