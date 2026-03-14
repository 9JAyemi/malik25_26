module seven_to_one_sva (
    input logic CLK,
    input logic RESETn,
    input logic [6:0] in1,
    input logic [6:0] in2,
    input logic [6:0] in3,
    input logic [6:0] in4,
    input logic [6:0] in5,
    input logic [6:0] in6,
    input logic [6:0] in7,
    input logic out
);
    // Derived column ANDs for bits [0:5]
    wire col0 = in1[0] & in2[0] & in3[0] & in4[0] & in5[0] & in6[0] & in7[0];
    wire col1 = in1[1] & in2[1] & in3[1] & in4[1] & in5[1] & in6[1] & in7[1];
    wire col2 = in1[2] & in2[2] & in3[2] & in4[2] & in5[2] & in6[2] & in7[2];
    wire col3 = in1[3] & in2[3] & in3[3] & in4[3] & in5[3] & in6[3] & in7[3];
    wire col4 = in1[4] & in2[4] & in3[4] & in4[4] & in5[4] & in6[4] & in7[4];
    wire col5 = in1[5] & in2[5] & in3[5] & in4[5] & in5[5] & in6[5] & in7[5];
    wire sop  = col0 | col1 | col2 | col3 | col4 | col5;

    // Out equals the OR of six 7-input AND columns (functional equivalence).
    check_out_equivalence: assert property (
        @(posedge CLK) disable iff (!RESETn) (out == sop)
    );

    // If all inputs' bit[0] are 1, out must be 1.
    check_out_when_col0_all_ones: assert property (
        @(posedge CLK) disable iff (!RESETn) col0 |=> out
    );

    // If all inputs' bit[1] are 1, out must be 1.
    check_out_when_col1_all_ones: assert property (
        @(posedge CLK) disable iff (!RESETn) col1 |=> out
    );

    // If all inputs' bit[2] are 1, out must be 1.
    check_out_when_col2_all_ones: assert property (
        @(posedge CLK) disable iff (!RESETn) col2 |=> out
    );

    // If all inputs' bit[3] are 1, out must be 1.
    check_out_when_col3_all_ones: assert property (
        @(posedge CLK) disable iff (!RESETn) col3 |=> out
    );

    // If all inputs' bit[4] are 1, out must be 1.
    check_out_when_col4_all_ones: assert property (
        @(posedge CLK) disable iff (!RESETn) col4 |=> out
    );

    // If all inputs' bit[5] are 1, out must be 1.
    check_out_when_col5_all_ones: assert property (
        @(posedge CLK) disable iff (!RESETn) col5 |=> out
    );

    // If no column is all ones, out must be 0.
    check_out_zero_when_no_column_all_ones: assert property (
        @(posedge CLK) disable iff (!RESETn) (!col0 && !col1 && !col2 && !col3 && !col4 && !col5) |=> (out == 1'b0)
    );

    // Out is stable when all lower 6 bits of all inputs are stable.
    check_out_stable_when_lower6_stable: assert property (
        @(posedge CLK) disable iff (!RESETn)
            ($stable(in1[5:0]) && $stable(in2[5:0]) && $stable(in3[5:0]) &&
             $stable(in4[5:0]) && $stable(in5[5:0]) && $stable(in6[5:0]) &&
             $stable(in7[5:0])) |=> $stable(out)
    );

    // Any change on out requires a change in some lower-6 input bit.
    check_out_change_requires_lower6_change: assert property (
        @(posedge CLK) disable iff (!RESETn)
            $changed(out) |=> !($stable(in1[5:0]) && $stable(in2[5:0]) && $stable(in3[5:0]) &&
                                $stable(in4[5:0]) && $stable(in5[5:0]) && $stable(in6[5:0]) &&
                                $stable(in7[5:0]))
    );
endmodule