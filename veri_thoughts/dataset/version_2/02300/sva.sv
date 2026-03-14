module MUXn_4_1_sva #(
    parameter MuxLen = 63
)(
    input logic clk,
    input logic rst_n,

    // DUT ports
    input logic [MuxLen:0] mux_in0,
    input logic [MuxLen:0] mux_in1,
    input logic [MuxLen:0] mux_in2,
    input logic [MuxLen:0] mux_in3,
    input logic [1:0]      mux_sel,
    input logic [MuxLen:0] mux_out
);

    ///// 4:1 mux select mapping /////
    // When mux_sel==00, output equals mux_in0.
    check_sel_00_maps_to_in0: assert property (
        @(posedge clk) disable iff (!rst_n) (mux_sel == 2'b00) |-> (mux_out == mux_in0)
    );

    // When mux_sel==01, output equals mux_in1.
    check_sel_01_maps_to_in1: assert property (
        @(posedge clk) disable iff (!rst_n) (mux_sel == 2'b01) |-> (mux_out == mux_in1)
    );

    // When mux_sel==10, output equals mux_in2.
    check_sel_10_maps_to_in2: assert property (
        @(posedge clk) disable iff (!rst_n) (mux_sel == 2'b10) |-> (mux_out == mux_in2)
    );

    // When mux_sel==11, output equals mux_in3.
    check_sel_11_maps_to_in3: assert property (
        @(posedge clk) disable iff (!rst_n) (mux_sel == 2'b11) |-> (mux_out == mux_in3)
    );

    ///// Functional equivalence to ternary expression /////
    // Output equals nested ternary of mux_sel bits.
    check_function_equivalence: assert property (
        @(posedge clk) disable iff (!rst_n)
        mux_out == (mux_sel[1] ? (mux_sel[0] ? mux_in3 : mux_in2)
                               : (mux_sel[0] ? mux_in1 : mux_in0))
    );

    ///// Stability given stable selection path /////
    // If sel==00 and both sel and mux_in0 are stable, output is stable.
    check_stable_out_when_00_path_stable: assert property (
        @(posedge clk) disable iff (!rst_n)
        (mux_sel == 2'b00 && $stable(mux_sel) && $stable(mux_in0)) |-> $stable(mux_out)
    );

    // If sel==01 and both sel and mux_in1 are stable, output is stable.
    check_stable_out_when_01_path_stable: assert property (
        @(posedge clk) disable iff (!rst_n)
        (mux_sel == 2'b01 && $stable(mux_sel) && $stable(mux_in1)) |-> $stable(mux_out)
    );

    // If sel==10 and both sel and mux_in2 are stable, output is stable.
    check_stable_out_when_10_path_stable: assert property (
        @(posedge clk) disable iff (!rst_n)
        (mux_sel == 2'b10 && $stable(mux_sel) && $stable(mux_in2)) |-> $stable(mux_out)
    );

    // If sel==11 and both sel and mux_in3 are stable, output is stable.
    check_stable_out_when_11_path_stable: assert property (
        @(posedge clk) disable iff (!rst_n)
        (mux_sel == 2'b11 && $stable(mux_sel) && $stable(mux_in3)) |-> $stable(mux_out)
    );

    ///// Simplifications when input pairs are equal /////
    // If upper select=0 and mux_in0==mux_in1, output equals that value.
    check_low_tree_pair_equal: assert property (
        @(posedge clk) disable iff (!rst_n)
        (mux_sel[1] == 1'b0 && (mux_in0 == mux_in1)) |-> (mux_out == mux_in0)
    );

    // If upper select=1 and mux_in2==mux_in3, output equals that value.
    check_high_tree_pair_equal: assert property (
        @(posedge clk) disable iff (!rst_n)
        (mux_sel[1] == 1'b1 && (mux_in2 == mux_in3)) |-> (mux_out == mux_in2)
    );

endmodule