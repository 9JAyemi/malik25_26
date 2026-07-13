module top_module_sva (
    input logic clk,
    // DUT ports
    input logic [3:0] in0,
    input logic [3:0] in1,
    input logic [3:0] in2,
    input logic [3:0] in3,
    input logic [1:0] sel,
    input logic [3:0] out,
    // Internal signals of top_module
    input logic [3:0] mux_out,
    input logic [3:0] rev_in
);
    ///// Multiplexer behavior /////
    // When sel==00, mux_out equals in0.
    check_mux_sel_00: assert property (
        @(posedge clk) disable iff (1'b0) (sel == 2'b00) |-> (mux_out === in0)
    );
    // When sel==01, mux_out equals in1.
    check_mux_sel_01: assert property (
        @(posedge clk) disable iff (1'b0) (sel == 2'b01) |-> (mux_out === in1)
    );
    // When sel==10, mux_out equals in2.
    check_mux_sel_10: assert property (
        @(posedge clk) disable iff (1'b0) (sel == 2'b10) |-> (mux_out === in2)
    );
    // When sel==11, mux_out equals in3.
    check_mux_sel_11: assert property (
        @(posedge clk) disable iff (1'b0) (sel == 2'b11) |-> (mux_out === in3)
    );

    ///// Reverse-input wiring /////
    // rev_in equals in0 due to truncation of {in3,in2,in1,in0} to 4 bits.
    check_rev_in_equals_in0: assert property (
        @(posedge clk) disable iff (1'b0) (rev_in === in0)
    );

    ///// Functional module behavior /////
    // out equals mux_out when mux_out > rev_in; else equals rev_in.
    check_func_out_def: assert property (
        @(posedge clk) disable iff (1'b0) out === ((mux_out > rev_in) ? mux_out : rev_in)
    );
    // out is always either mux_out or rev_in.
    check_func_out_is_one_of_inputs: assert property (
        @(posedge clk) disable iff (1'b0) (out === mux_out) || (out === rev_in)
    );
    // If mux_out == rev_in, out equals that common value.
    check_func_out_when_equal: assert property (
        @(posedge clk) disable iff (1'b0) (mux_out === rev_in) |-> (out === rev_in)
    );

    ///// Top-level composed behavior /////
    // When sel==00, out equals in0.
    check_top_sel00_out_in0: assert property (
        @(posedge clk) disable iff (1'b0) (sel == 2'b00) |-> (out === in0)
    );
    // When sel==01, out equals (in1 > in0) ? in1 : in0.
    check_top_sel01_out: assert property (
        @(posedge clk) disable iff (1'b0) (sel == 2'b01) |-> (out === ((in1 > in0) ? in1 : in0))
    );
    // When sel==10, out equals (in2 > in0) ? in2 : in0.
    check_top_sel10_out: assert property (
        @(posedge clk) disable iff (1'b0) (sel == 2'b10) |-> (out === ((in2 > in0) ? in2 : in0))
    );
    // When sel==11, out equals (in3 > in0) ? in3 : in0.
    check_top_sel11_out: assert property (
        @(posedge clk) disable iff (1'b0) (sel == 2'b11) |-> (out === ((in3 > in0) ? in3 : in0))
    );
endmodule