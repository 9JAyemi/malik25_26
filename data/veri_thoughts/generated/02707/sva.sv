module mux_min_sva (
    input logic clk,
    input logic [2:0] vec,
    input logic select,
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [7:0] c,
    input logic [7:0] d,
    input logic [2:0] outv,
    input logic o2,
    input logic o1,
    input logic o0,
    input logic [7:0] min
);

    ///// Multiplexer (outv/o2/o1/o0) /////
    // outv must be three copies of (vec[2] | vec[1] | vec[0]).
    check_outv_replication: assert property (
        @(posedge clk) outv == {3{|vec}}
    );

    // o2 equals outv[2].
    check_o2_matches_outv2: assert property (
        @(posedge clk) o2 == outv[2]
    );

    // o1 equals outv[1].
    check_o1_matches_outv1: assert property (
        @(posedge clk) o1 == outv[1]
    );

    // o0 equals outv[0].
    check_o0_matches_outv0: assert property (
        @(posedge clk) o0 == outv[0]
    );

    // If all vec bits are 0 then outv is 3'b000.
    check_outv_all_zero_when_vec_zero: assert property (
        @(posedge clk) (~|vec) |-> (outv == 3'b000)
    );

    // If any vec bit is 1 then outv is 3'b111.
    check_outv_all_one_when_any_vec_high: assert property (
        @(posedge clk) (|vec) |-> (outv == 3'b111)
    );

    // Changing only 'select' does not change outputs (select is unused).
    check_outputs_independent_of_select: assert property (
        @(posedge clk)
            $changed(select) && $stable(vec) && $stable(a) && $stable(b) && $stable(c) && $stable(d)
        |-> $stable(outv) && $stable(o2) && $stable(o1) && $stable(o0) && $stable(min)
    );

    ///// Minimum-of-four (min) /////
    // min is less than or equal to a.
    check_min_le_a: assert property (
        @(posedge clk) min <= a
    );

    // min is less than or equal to b.
    check_min_le_b: assert property (
        @(posedge clk) min <= b
    );

    // min is less than or equal to c.
    check_min_le_c: assert property (
        @(posedge clk) min <= c
    );

    // min is less than or equal to d.
    check_min_le_d: assert property (
        @(posedge clk) min <= d
    );

    // min equals one of the inputs a/b/c/d.
    check_min_is_input: assert property (
        @(posedge clk) (min == a) || (min == b) || (min == c) || (min == d)
    );

    // If a is strictly less than b,c,d then min equals a.
    check_unique_min_a: assert property (
        @(posedge clk) (a < b) && (a < c) && (a < d) |-> (min == a)
    );

    // If b is strictly less than a,c,d then min equals b.
    check_unique_min_b: assert property (
        @(posedge clk) (b < a) && (b < c) && (b < d) |-> (min == b)
    );

    // If c is strictly less than a,b,d then min equals c.
    check_unique_min_c: assert property (
        @(posedge clk) (c < a) && (c < b) && (c < d) |-> (min == c)
    );

    // If d is strictly less than a,b,c then min equals d.
    check_unique_min_d: assert property (
        @(posedge clk) (d < a) && (d < b) && (d < c) |-> (min == d)
    );

    // min matches the exact pairwise comparator/mux structure.
    check_min_structural_equivalence: assert property (
        @(posedge clk)
            min == ( (((a < b) ? a : b) < ((c < d) ? c : d))
                     ? ((a < b) ? a : b)
                     : ((c < d) ? c : d) )
    );

endmodule