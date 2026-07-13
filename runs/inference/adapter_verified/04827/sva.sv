module mux4to1_sva (
    input logic clk,
    input logic in0,
    input logic in1,
    input logic in2,
    input logic in3,
    input logic sel0,
    input logic sel1,
    input logic out
);

// No reset in RTL; sample combinational behavior on clk.

    // When sel1==0, out selects between in0/in1 based on sel0.
    check_sel1_low_selects_in0_in1: assert property (
        @(posedge clk) (sel1 == 1'b0) |-> (out == (sel0 ? in1 : in0))
    );

// When sel1==1, out selects between in2/in3 based on sel0.
    check_sel1_high_selects_in2_in3: assert property (
        @(posedge clk) (sel1 == 1'b1) |-> (out == (sel0 ? in3 : in2))
    );

// When sel0==0, out selects between in0/in2 based on sel1.
    check_sel0_low_selects_in0_in2: assert property (
        @(posedge clk) (sel0 == 1'b0) |-> (out == (sel1 ? in2 : in0))
    );

// When sel0==1, out selects between in1/in3 based on sel1.
    check_sel0_high_selects_in1_in3: assert property (
        @(posedge clk) (sel0 == 1'b1) |-> (out == (sel1 ? in3 : in1))
    );

// With sel1==0 and sel0==0, out equals in0.
    check_sel00_out_in0: assert property (
        @(posedge clk) (sel1 == 1'b0 && sel0 == 1'b0) |-> (out == in0)
    );

// With sel1==0 and sel0==1, out equals in1.
    check_sel01_out_in1: assert property (
        @(posedge clk) (sel1 == 1'b0 && sel0 == 1'b1) |-> (out == in1)
    );

// With sel1==1 and sel0==0, out equals in2.
    check_sel10_out_in2: assert property (
        @(posedge clk) (sel1 == 1'b1 && sel0 == 1'b0) |-> (out == in2)
    );

// With sel1==1 and sel0==1, out equals in3.
    check_sel11_out_in3: assert property (
        @(posedge clk) (sel1 == 1'b1 && sel0 == 1'b1) |-> (out == in3)
    );

endmodule
