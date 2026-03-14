module mux_4to1_sva (
    input logic [3:0] in0,
    input logic [3:0] in1,
    input logic [3:0] in2,
    input logic [3:0] in3,
    input logic [1:0] sel,
    input logic clk,
    input logic [3:0] out,
    // Internal DUT signals (optional to connect via bind for stronger checks)
    input logic [3:0] stage1_out,
    input logic [3:0] stage2_out
);
    ///// Combinational select correctness at sampling /////
    // When sel==00, stage1_out equals in0 at the sampling edge.
    check_stage1_sel_00: assert property (
        @(posedge clk) (sel == 2'b00) |-> (stage1_out == in0)
    );
    // When sel==01, stage1_out equals in1 at the sampling edge.
    check_stage1_sel_01: assert property (
        @(posedge clk) (sel == 2'b01) |-> (stage1_out == in1)
    );
    // When sel==10, stage1_out equals in2 at the sampling edge.
    check_stage1_sel_10: assert property (
        @(posedge clk) (sel == 2'b10) |-> (stage1_out == in2)
    );
    // When sel==11, stage1_out equals in3 at the sampling edge.
    check_stage1_sel_11: assert property (
        @(posedge clk) (sel == 2'b11) |-> (stage1_out == in3)
    );

    ///// Pipeline register behavior /////
    // stage2_out at the next cycle equals stage1_out from the current cycle.
    check_stage2_captures_stage1: assert property (
        @(posedge clk) 1'b1 |-> ##1 (stage2_out == $past(stage1_out))
    );
    // out continuously reflects stage2_out.
    check_out_equals_stage2: assert property (
        @(posedge clk) out == stage2_out
    );

    ///// End-to-end 1-cycle pipeline from inputs to out /////
    // If sel==00 this cycle, out equals in0 from this cycle on the next cycle.
    check_out_pipeline_sel_00: assert property (
        @(posedge clk) (sel == 2'b00) |=> (out == $past(in0))
    );
    // If sel==01 this cycle, out equals in1 from this cycle on the next cycle.
    check_out_pipeline_sel_01: assert property (
        @(posedge clk) (sel == 2'b01) |=> (out == $past(in1))
    );
    // If sel==10 this cycle, out equals in2 from this cycle on the next cycle.
    check_out_pipeline_sel_10: assert property (
        @(posedge clk) (sel == 2'b10) |=> (out == $past(in2))
    );
    // If sel==11 this cycle, out equals in3 from this cycle on the next cycle.
    check_out_pipeline_sel_11: assert property (
        @(posedge clk) (sel == 2'b11) |=> (out == $past(in3))
    );
endmodule