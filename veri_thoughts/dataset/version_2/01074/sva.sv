module mux4to1_sva (
    input logic CLK,
    input logic [3:0] in0,
    input logic [3:0] in1,
    input logic [3:0] in2,
    input logic [3:0] in3,
    input logic [1:0] sel,
    input logic [3:0] out
);
    ///// Functional mapping /////
    // When sel==00, out equals in0.
    select_00_routes_in0: assert property (
        @(posedge CLK) (sel == 2'b00) |-> (out == in0)
    );
    // When sel==01, out equals in1.
    select_01_routes_in1: assert property (
        @(posedge CLK) (sel == 2'b01) |-> (out == in1)
    );
    // When sel==10, out equals in2.
    select_10_routes_in2: assert property (
        @(posedge CLK) (sel == 2'b10) |-> (out == in2)
    );
    // When sel==11, out equals in3.
    select_11_routes_in3: assert property (
        @(posedge CLK) (sel == 2'b11) |-> (out == in3)
    );

    ///// Stability and dependency /////
    // If sel and all inputs are stable, out is stable.
    all_stable_implies_out_stable: assert property (
        @(posedge CLK) $stable(sel) && $stable(in0) && $stable(in1) && $stable(in2) && $stable(in3) |-> $stable(out)
    );
    // If sel==00 holds and in0 is stable, out is stable.
    stable_when_sel0_and_in0_stable: assert property (
        @(posedge CLK) (sel == 2'b00) && $stable(sel) && $stable(in0) |-> $stable(out)
    );
    // If sel==01 holds and in1 is stable, out is stable.
    stable_when_sel1_and_in1_stable: assert property (
        @(posedge CLK) (sel == 2'b01) && $stable(sel) && $stable(in1) |-> $stable(out)
    );
    // If sel==10 holds and in2 is stable, out is stable.
    stable_when_sel2_and_in2_stable: assert property (
        @(posedge CLK) (sel == 2'b10) && $stable(sel) && $stable(in2) |-> $stable(out)
    );
    // If sel==11 holds and in3 is stable, out is stable.
    stable_when_sel3_and_in3_stable: assert property (
        @(posedge CLK) (sel == 2'b11) && $stable(sel) && $stable(in3) |-> $stable(out)
    );

    ///// Change propagation /////
    // If sel==00 holds and in0 changes, out changes.
    change_propagation_sel0: assert property (
        @(posedge CLK) (sel == 2'b00) && $stable(sel) && $changed(in0) |-> $changed(out)
    );
    // If sel==01 holds and in1 changes, out changes.
    change_propagation_sel1: assert property (
        @(posedge CLK) (sel == 2'b01) && $stable(sel) && $changed(in1) |-> $changed(out)
    );
    // If sel==10 holds and in2 changes, out changes.
    change_propagation_sel2: assert property (
        @(posedge CLK) (sel == 2'b10) && $stable(sel) && $changed(in2) |-> $changed(out)
    );
    // If sel==11 holds and in3 changes, out changes.
    change_propagation_sel3: assert property (
        @(posedge CLK) (sel == 2'b11) && $stable(sel) && $changed(in3) |-> $changed(out)
    );
endmodule