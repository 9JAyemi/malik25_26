module mux4_sva (
    input logic clk,           // sampling clock for assertions (DUT has no clock)
    input logic [3:0] in0,
    input logic [3:0] in1,
    input logic [3:0] in2,
    input logic [3:0] in3,
    input logic [1:0] sel,
    input logic [3:0] out
);
    ///// Combinational mux mapping checks /////
    // When sel==00, out equals in0 at the sample edge.
    check_sel_00_maps_to_in0: assert property (
        @(posedge clk) (sel == 2'b00) |=> (out == in0)
    );
    // When sel==01, out equals in1 at the sample edge.
    check_sel_01_maps_to_in1: assert property (
        @(posedge clk) (sel == 2'b01) |=> (out == in1)
    );
    // When sel==10, out equals in2 at the sample edge.
    check_sel_10_maps_to_in2: assert property (
        @(posedge clk) (sel == 2'b10) |=> (out == in2)
    );
    // When sel==11, out equals in3 at the sample edge.
    check_sel_11_maps_to_in3: assert property (
        @(posedge clk) (sel == 2'b11) |=> (out == in3)
    );

    ///// Stability under stable selection /////
    // If sel==00 and both sel and in0 are stable, out remains stable.
    stable_out_when_00_and_in0_stable: assert property (
        @(posedge clk) (sel == 2'b00) && $stable(sel) && $stable(in0) |=> $stable(out)
    );
    // If sel==01 and both sel and in1 are stable, out remains stable.
    stable_out_when_01_and_in1_stable: assert property (
        @(posedge clk) (sel == 2'b01) && $stable(sel) && $stable(in1) |=> $stable(out)
    );
    // If sel==10 and both sel and in2 are stable, out remains stable.
    stable_out_when_10_and_in2_stable: assert property (
        @(posedge clk) (sel == 2'b10) && $stable(sel) && $stable(in2) |=> $stable(out)
    );
    // If sel==11 and both sel and in3 are stable, out remains stable.
    stable_out_when_11_and_in3_stable: assert property (
        @(posedge clk) (sel == 2'b11) && $stable(sel) && $stable(in3) |=> $stable(out)
    );
endmodule