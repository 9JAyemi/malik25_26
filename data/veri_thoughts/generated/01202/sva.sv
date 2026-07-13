module mux3to1_sva (
    input logic clk,
    input logic [1:0] sel,
    input logic in0,
    input logic in1,
    input logic in2,
    input logic out
);

    // sel==0 routes in0 to out.
    check_sel0_routes_in0: assert property (
        @(posedge clk) disable iff (1'b0) (sel == 2'd0) |-> (out == in0)
    );

    // sel==1 routes in1 to out.
    check_sel1_routes_in1: assert property (
        @(posedge clk) disable iff (1'b0) (sel == 2'd1) |-> (out == in1)
    );

    // sel==2 routes in2 to out.
    check_sel2_routes_in2: assert property (
        @(posedge clk) disable iff (1'b0) (sel == 2'd2) |-> (out == in2)
    );

    // sel==3 drives out low (default branch).
    check_sel3_routes_zero: assert property (
        @(posedge clk) disable iff (1'b0) (sel == 2'd3) |-> (out == 1'b0)
    );

    // If sel and selected source are stable, out remains stable.
    check_stable_out_when_sel_and_source_stable: assert property (
        @(posedge clk) disable iff (1'b0)
        ($stable(sel) && ((sel==2'd0 && $stable(in0)) ||
                          (sel==2'd1 && $stable(in1)) ||
                          (sel==2'd2 && $stable(in2)) ||
                          (sel==2'd3)))
        |-> $stable(out)
    );

    // If out is LOW, then either the selected input is LOW or sel==3.
    check_out_zero_implies_selected_zero_or_default: assert property (
        @(posedge clk) disable iff (1'b0)
        (out == 1'b0) |-> ((sel==2'd0 && in0==1'b0) ||
                           (sel==2'd1 && in1==1'b0) ||
                           (sel==2'd2 && in2==1'b0) ||
                           (sel==2'd3))
    );

    // If out is HIGH, then the selected input is HIGH (sel cannot be 3).
    check_out_one_implies_selected_one: assert property (
        @(posedge clk) disable iff (1'b0)
        (out == 1'b1) |-> ((sel==2'd0 && in0==1'b1) ||
                           (sel==2'd1 && in1==1'b1) ||
                           (sel==2'd2 && in2==1'b1))
    );

endmodule