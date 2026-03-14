module velocityControlHdl_MinMax_sva (
    input logic clk,
    input  signed [17:0] in0,
    input  signed [17:0] in1,
    input  signed [17:0] in2,
    input  signed [17:0] out0
);
    // Out must equal one of the inputs (min is selected from inputs).
    check_out_is_from_inputs: assert property (
        @(posedge clk) disable iff (1'b0) (out0 == in0) || (out0 == in1) || (out0 == in2)
    );

    // Out is less than or equal to in0.
    check_out_le_in0: assert property (
        @(posedge clk) disable iff (1'b0) out0 <= in0
    );

    // Out is less than or equal to in1.
    check_out_le_in1: assert property (
        @(posedge clk) disable iff (1'b0) out0 <= in1
    );

    // Out is less than or equal to in2.
    check_out_le_in2: assert property (
        @(posedge clk) disable iff (1'b0) out0 <= in2
    );

    // If in0 is less than or equal to both in1 and in2, out equals in0.
    select_in0_when_min: assert property (
        @(posedge clk) disable iff (1'b0) ((in0 <= in1) && (in0 <= in2)) |-> (out0 == in0)
    );

    // If in1 is strictly less than in0 and less than or equal to in2, out equals in1.
    select_in1_when_strict_min: assert property (
        @(posedge clk) disable iff (1'b0) ((in1 < in0) && (in1 <= in2)) |-> (out0 == in1)
    );

    // If in2 is strictly less than both in0 and in1, out equals in2.
    select_in2_when_strict_min: assert property (
        @(posedge clk) disable iff (1'b0) ((in2 < in0) && (in2 < in1)) |-> (out0 == in2)
    );

    // If out equals in0, then in0 is less than or equal to both in1 and in2.
    out_eq_in0_implies_in0_min: assert property (
        @(posedge clk) disable iff (1'b0) (out0 == in0) |-> ((in0 <= in1) && (in0 <= in2))
    );

    // If out equals in1, then in1 is strictly less than in0 and less than or equal to in2.
    out_eq_in1_implies_in1_min: assert property (
        @(posedge clk) disable iff (1'b0) (out0 == in1) |-> ((in1 < in0) && (in1 <= in2))
    );

    // If out equals in2, then in2 is strictly less than both in0 and in1.
    out_eq_in2_implies_in2_min: assert property (
        @(posedge clk) disable iff (1'b0) (out0 == in2) |-> ((in2 < in0) && (in2 < in1))
    );

    // Tie between in0 and in1 (and <= in2) selects in0 due to <= tie-break.
    tie_in0_in1_prefers_in0: assert property (
        @(posedge clk) disable iff (1'b0) ((in0 == in1) && (in0 <= in2)) |-> (out0 == in0)
    );

    // Tie between in0 and in2 (and <= in1) selects in0 due to <= tie-break.
    tie_in0_in2_prefers_in0: assert property (
        @(posedge clk) disable iff (1'b0) ((in0 == in2) && (in0 <= in1)) |-> (out0 == in0)
    );

    // Tie between in1 and in2, both less than in0, selects in1 due to <= tie-break.
    tie_in1_in2_prefers_in1: assert property (
        @(posedge clk) disable iff (1'b0) ((in1 == in2) && (in1 < in0)) |-> (out0 == in1)
    );

    // All inputs equal selects in0 due to tie-break ordering.
    all_equal_prefers_in0: assert property (
        @(posedge clk) disable iff (1'b0) ((in0 == in1) && (in1 == in2)) |-> (out0 == in0)
    );
endmodule