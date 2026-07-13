module mux_4to1_en_sva (
    input logic clk,               // verification clock (RTL has no clock/reset)
    input logic [3:0] in0, in1, in2, in3,
    input logic [1:0] sel,
    input logic en,
    input logic [3:0] out
);
    // Analysis: No clock/reset in RTL; purely combinational always @(*); out = en ? selected in : 4'b0000.

    // en low forces out to zero.
    check_out_zero_when_disabled: assert property (
        @(posedge clk) disable iff (1'b0) (!en) |-> (out == 4'b0000)
    );

    // When en=1 and sel==00, out equals in0.
    check_sel_00_route: assert property (
        @(posedge clk) disable iff (1'b0) (en && (sel == 2'b00)) |-> (out == in0)
    );

    // When en=1 and sel==01, out equals in1.
    check_sel_01_route: assert property (
        @(posedge clk) disable iff (1'b0) (en && (sel == 2'b01)) |-> (out == in1)
    );

    // When en=1 and sel==10, out equals in2.
    check_sel_10_route: assert property (
        @(posedge clk) disable iff (1'b0) (en && (sel == 2'b10)) |-> (out == in2)
    );

    // When en=1 and sel==11, out equals in3.
    check_sel_11_route: assert property (
        @(posedge clk) disable iff (1'b0) (en && (sel == 2'b11)) |-> (out == in3)
    );

    // Functional equivalence to the mux with enable.
    check_functional_equivalence: assert property (
        @(posedge clk) disable iff (1'b0)
            out == (en ? (sel == 2'b00 ? in0 :
                          sel == 2'b01 ? in1 :
                          sel == 2'b10 ? in2 : in3)
                      : 4'b0000)
    );

    // If inputs, sel, and en are stable, out remains stable (pure combinational).
    check_out_stable_when_inputs_stable: assert property (
        @(posedge clk) disable iff (1'b0) $stable({en, sel, in0, in1, in2, in3}) |-> $stable(out)
    );

endmodule