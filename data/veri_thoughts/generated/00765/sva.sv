module mux_4to1_sva (
    input logic clk,
    input logic [3:0] in0,
    input logic [3:0] in1,
    input logic [3:0] in2,
    input logic [3:0] in3,
    input logic [1:0] sel,
    input logic enable,
    input logic [3:0] out
);
    // Out matches the mux+enable function exactly.
    check_mux_function: assert property (
        @(posedge clk)
        out === (enable ? (sel == 2'b00 ? in0 :
                           sel == 2'b01 ? in1 :
                           sel == 2'b10 ? in2 : in3)
                       : 4'b0)
    );

    // When disabled, out must be zero.
    check_out_zero_when_disabled: assert property (
        @(posedge clk) (!enable) |-> (out === 4'b0)
    );

    // When enabled and sel==00, out equals in0.
    check_sel00_routing: assert property (
        @(posedge clk) (enable && (sel == 2'b00)) |-> (out === in0)
    );

    // When enabled and sel==01, out equals in1.
    check_sel01_routing: assert property (
        @(posedge clk) (enable && (sel == 2'b01)) |-> (out === in1)
    );

    // When enabled and sel==10, out equals in2.
    check_sel10_routing: assert property (
        @(posedge clk) (enable && (sel == 2'b10)) |-> (out === in2)
    );

    // When enabled and sel==11, out equals in3.
    check_sel11_routing: assert property (
        @(posedge clk) (enable && (sel == 2'b11)) |-> (out === in3)
    );

    // If all inputs are equal and enabled, out equals that common value.
    check_equal_inputs_collapse: assert property (
        @(posedge clk) (enable && (in0 === in1) && (in1 === in2) && (in2 === in3)) |-> (out === in0)
    );

    // If enabled and out is zero, the selected input must be zero.
    check_zero_out_implies_zero_selected_input: assert property (
        @(posedge clk)
        (enable && (out === 4'b0)) |-> (
            (sel == 2'b00) ? (in0 === 4'b0) :
            (sel == 2'b01) ? (in1 === 4'b0) :
            (sel == 2'b10) ? (in2 === 4'b0) :
                             (in3 === 4'b0)
        )
    );
endmodule