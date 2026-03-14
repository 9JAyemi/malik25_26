module magnitude_comparator_sva (
    input logic CLK,
    input logic [3:0] a,
    input logic [3:0] b,
    input logic [1:0] out
);
    ///// Magnitude comparison encoding /////
    // 'out' matches the ternary mapping of a and b.
    check_functional_equivalence: assert property (
        @(posedge CLK) out == ((a > b) ? 2'b01 : (a < b) ? 2'b10 : 2'b00)
    );
    // out[0] is 1 iff a > b.
    check_out0_maps_gt: assert property (
        @(posedge CLK) out[0] == (a > b)
    );
    // out[1] is 1 iff a < b.
    check_out1_maps_lt: assert property (
        @(posedge CLK) out[1] == (a < b)
    );
    // out never takes invalid value 2'b11.
    check_out_not_11: assert property (
        @(posedge CLK) out != 2'b11
    );
    // If a > b then out must be 2'b01.
    check_gt_implies_out01: assert property (
        @(posedge CLK) (a > b) |-> (out == 2'b01)
    );
    // If a < b then out must be 2'b10.
    check_lt_implies_out10: assert property (
        @(posedge CLK) (a < b) |-> (out == 2'b10)
    );
    // If a == b then out must be 2'b00.
    check_eq_implies_out00: assert property (
        @(posedge CLK) (a == b) |-> (out == 2'b00)
    );
    // If out is 2'b01 then a must be > b.
    check_out01_implies_gt: assert property (
        @(posedge CLK) (out == 2'b01) |-> (a > b)
    );
    // If out is 2'b10 then a must be < b.
    check_out10_implies_lt: assert property (
        @(posedge CLK) (out == 2'b10) |-> (a < b)
    );
    // If out is 2'b00 then a must equal b.
    check_out00_implies_eq: assert property (
        @(posedge CLK) (out == 2'b00) |-> (a == b)
    );
endmodule