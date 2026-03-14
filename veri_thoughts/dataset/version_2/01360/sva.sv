module mux4to1_sva (
    input logic in0,
    input logic in1,
    input logic in2,
    input logic in3,
    input logic sel0,
    input logic sel1,
    input logic clk,
    input logic out
);
    // When sel==00, next-cycle out equals in0 sampled this cycle.
    sel00_routes_in0: assert property (
        @(posedge clk) (sel1 == 1'b0 && sel0 == 1'b0) |=> (out == $past(in0))
    );

    // When sel==01, next-cycle out equals in1 sampled this cycle.
    sel01_routes_in1: assert property (
        @(posedge clk) (sel1 == 1'b0 && sel0 == 1'b1) |=> (out == $past(in1))
    );

    // When sel==10, next-cycle out equals in2 sampled this cycle.
    sel10_routes_in2: assert property (
        @(posedge clk) (sel1 == 1'b1 && sel0 == 1'b0) |=> (out == $past(in2))
    );

    // When sel==11, next-cycle out equals in3 sampled this cycle.
    sel11_routes_in3: assert property (
        @(posedge clk) (sel1 == 1'b1 && sel0 == 1'b1) |=> (out == $past(in3))
    );

    // On every cycle, out equals the input selected in the previous cycle.
    out_matches_prev_selected_input: assert property (
        @(posedge clk) 1'b1 |=> out == $past(
            (sel1 == 1'b0 && sel0 == 1'b0) ? in0 :
            (sel1 == 1'b0 && sel0 == 1'b1) ? in1 :
            (sel1 == 1'b1 && sel0 == 1'b0) ? in2 : in3
        )
    );
endmodule