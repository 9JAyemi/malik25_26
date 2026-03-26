module oh_mux9_sva #(parameter DW = 1) (
    input logic          clk,
    input logic          sel8,
    input logic          sel7,
    input logic          sel6,
    input logic          sel5,
    input logic          sel4,
    input logic          sel3,
    input logic          sel2,
    input logic          sel1,
    input logic          sel0,
    input logic [DW-1:0] in8,
    input logic [DW-1:0] in7,
    input logic [DW-1:0] in6,
    input logic [DW-1:0] in5,
    input logic [DW-1:0] in4,
    input logic [DW-1:0] in3,
    input logic [DW-1:0] in2,
    input logic [DW-1:0] in1,
    input logic [DW-1:0] in0,
    input logic [DW-1:0] out
);

    // Output must equal the OR of all selected inputs.
    check_out_matches_selected_or: assert property (
        @(posedge clk)
        out == (({DW{sel0}} & in0) |
                ({DW{sel1}} & in1) |
                ({DW{sel2}} & in2) |
                ({DW{sel3}} & in3) |
                ({DW{sel4}} & in4) |
                ({DW{sel5}} & in5) |
                ({DW{sel6}} & in6) |
                ({DW{sel7}} & in7) |
                ({DW{sel8}} & in8))
    );

    // With no selects asserted, output must be zero.
    check_no_selects_drive_zero: assert property (
        @(posedge clk)
        (!(sel0 || sel1 || sel2 || sel3 || sel4 || sel5 || sel6 || sel7 || sel8))
        |-> (out == {DW{1'b0}})
    );

    // If only sel0 is asserted, output must equal in0.
    check_only_sel0_passes_in0: assert property (
        @(posedge clk)
        (sel0 && !(sel1 || sel2 || sel3 || sel4 || sel5 || sel6 || sel7 || sel8))
        |-> (out == in0)
    );

    // If only sel1 is asserted, output must equal in1.
    check_only_sel1_passes_in1: assert property (
        @(posedge clk)
        (sel1 && !(sel0 || sel2 || sel3 || sel4 || sel5 || sel6 || sel7 || sel8))
        |-> (out == in1)
    );

    // If only sel2 is asserted, output must equal in2.
    check_only_sel2_passes_in2: assert property (
        @(posedge clk)
        (sel2 && !(sel0 || sel1 || sel3 || sel4 || sel5 || sel6 || sel7 || sel8))
        |-> (out == in2)
    );

    // If only sel3 is asserted, output must equal in3.
    check_only_sel3_passes_in3: assert property (
        @(posedge clk)
        (sel3 && !(sel0 || sel1 || sel2 || sel4 || sel5 || sel6 || sel7 || sel8))
        |-> (out == in3)
    );

    // If only sel4 is asserted, output must equal in4.
    check_only_sel4_passes_in4: assert property (
        @(posedge clk)
        (sel4 && !(sel0 || sel1 || sel2 || sel3 || sel5 || sel6 || sel7 || sel8))
        |-> (out == in4)
    );

    // If only sel5 is asserted, output must equal in5.
    check_only_sel5_passes_in5: assert property (
        @(posedge clk)
        (sel5 && !(sel0 || sel1 || sel2 || sel3 || sel4 || sel6 || sel7 || sel8))
        |-> (out == in5)
    );

    // If only sel6 is asserted, output must equal in6.
    check_only_sel6_passes_in6: assert property (
        @(posedge clk)
        (sel6 && !(sel0 || sel1 || sel2 || sel3 || sel4 || sel5 || sel7 || sel8))
        |-> (out == in6)
    );

    // If only sel7 is asserted, output must equal in7.
    check_only_sel7_passes_in7: assert property (
        @(posedge clk)
        (sel7 && !(sel0 || sel1 || sel2 || sel3 || sel4 || sel5 || sel6 || sel8))
        |-> (out == in7)
    );

    // If only sel8 is asserted, output must equal in8.
    check_only_sel8_passes_in8: assert property (
        @(posedge clk)
        (sel8 && !(sel0 || sel1 || sel2 || sel3 || sel4 || sel5 || sel6 || sel7))
        |-> (out == in8)
    );

endmodule