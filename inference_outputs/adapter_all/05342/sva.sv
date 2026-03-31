module top_module_sva (
    input logic [3:0] in1,
    input logic [3:0] in2,
    input logic [3:0] out,
    input logic [3:0] max_out
);
    // out equals in1 + in2 (4-bit wraparound).
    check_out_sum: assert property (
        @(posedge in1[0]) out == (in1 + in2)
    );

    // max_out equals max(out, out + in2) (4-bit wraparound).
    check_max_out_function: assert property (
        @(posedge in1[0]) max_out == ((out > (out + in2)) ? out : (out + in2))
    );

    // max_out equals max(in1, in2) (4-bit wraparound).
    check_max_out_matches_inputs: assert property (
        @(posedge in1[0]) max_out == ((in1 > in2) ? in1 : in2)
    );

    // max_out is at least in1 (4-bit wraparound).
    check_max_out_ge_in1: assert property (
        @(posedge in1[0]) max_out >= in1
    );

    // max_out is at least in2 (4-bit wraparound).
    check_max_out_ge_in2: assert property (
        @(posedge in1[0]) max_out >= in2
    );

    // If in1 >= in2, max_out equals in1 (4-bit wraparound).
    check_max_when_in1_ge_in2: assert property (
        @(posedge in1[0]) (in1 >= in2) |-> (max_out == in1)
    );

    // If in1 < in2, max_out equals in2 (4-bit wraparound).
    check_max_when_in1_lt_in2: assert property (
        @(posedge in1[0]) (in1 < in2) |-> (max_out == in2)
    );

    // If in1 == in2, max_out equals in1 (4-bit wraparound).
    check_max_when_equal: assert property (
        @(posedge in1[0]) (in1 == in2) |-> (max_out == in1)
    );

    // max_out is never less than in1 (4-bit wraparound).
    check_max_out_ge_in1_direct: assert property (
        @(posedge in1[0]) max_out >= in1
    );

    // max_out is never less than in2 (4-bit wraparound).
    check_max_out_ge_in2_direct: assert property (
        @(posedge in1[0]) max_out >= in2
    );
endmodule