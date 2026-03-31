module DEMUX_3to8_sva (
    input logic clk,
    input logic in,
    input logic sel2,
    input logic sel1,
    input logic sel0,
    input logic out0,
    input logic out1,
    input logic out2,
    input logic out3,
    input logic out4,
    input logic out5,
    input logic out6,
    input logic out7
);

    // out0 is high only when the select vector is 000.
    check_out0_decode: assert property (
        @(posedge clk) out0 == ((sel2 == 1'b0) && (sel1 == 1'b0) && (sel0 == 1'b0))
    );

    // out1 is high only when the select vector is 001.
    check_out1_decode: assert property (
        @(posedge clk) out1 == ((sel2 == 1'b0) && (sel1 == 1'b0) && (sel0 == 1'b1))
    );

    // out2 is high only when the select vector is 010.
    check_out2_decode: assert property (
        @(posedge clk) out2 == ((sel2 == 1'b0) && (sel1 == 1'b1) && (sel0 == 1'b0))
    );

    // out3 is high only when the select vector is 011.
    check_out3_decode: assert property (
        @(posedge clk) out3 == ((sel2 == 1'b0) && (sel1 == 1'b1) && (sel0 == 1'b1))
    );

    // out4 is high only when the select vector is 100.
    check_out4_decode: assert property (
        @(posedge clk) out4 == ((sel2 == 1'b1) && (sel1 == 1'b0) && (sel0 == 1'b0))
    );

    // out5 is high only when the select vector is 101.
    check_out5_decode: assert property (
        @(posedge clk) out5 == ((sel2 == 1'b1) && (sel1 == 1'b0) && (sel0 == 1'b1))
    );

    // out6 is high only when the select vector is 110.
    check_out6_decode: assert property (
        @(posedge clk) out6 == ((sel2 == 1'b1) && (sel1 == 1'b1) && (sel0 == 1'b0))
    );

    // out7 is high only when the select vector is 111.
    check_out7_decode: assert property (
        @(posedge clk) out7 == ((sel2 == 1'b1) && (sel1 == 1'b1) && (sel0 == 1'b1))
    );

    // Exactly one output is high for every input combination.
    check_onehot_output: assert property (
        @(posedge clk) $onehot({out7, out6, out5, out4, out3, out2, out1, out0})
    );

    // The outputs always match the selected input bit.
    check_selected_output_matches_input: assert property (
        @(posedge clk)
        $onehot({sel2, sel1, sel0}) |-> (
            (sel2 == 1'b0 && sel1 == 1'b0 && sel0 == 1'b0) ? (out0 == in) :
            (sel2 == 1'b0 && sel1 == 1'b0 && sel0 == 1'b1) ? (out1 == in) :
            (sel2 == 1'b0 && sel1 == 1'b1 && sel0 == 1'b0) ? (out2 == in) :
            (sel2 == 1'b0 && sel1 == 1'b1 && sel0 == 1'b1) ? (out3 == in) :
            (sel2 == 1'b1 && sel1 == 1'b0 && sel0 == 1'b0) ? (out4 == in) :
            (sel2 == 1'b1 && sel1 == 1'b0 && sel0 == 1'b1) ? (out5 == in) :
            (sel2 == 1'b1 && sel1 == 1'b1 && sel0 == 1'b0) ? (out6 == in) :
            (sel2 == 1'b1 && sel1 == 1'b1 && sel0 == 1'b1) ? (out7 == in) : 1'b1
        )
    );

endmodule