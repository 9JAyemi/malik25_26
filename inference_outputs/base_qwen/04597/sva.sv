module mux_2_1_assertions(
    input logic CLK,
    input logic RSTn,
    input logic sel,
    input logic in0,
    input logic in1,
    input logic out
);
    // Sequential logic is not present, so all assertions will be clocked.

    // The output should be 1 if sel is 0 and in0 is 1, otherwise 0.
    mux_output_check: assert property (
        @(posedge CLK) disable iff (!RSTn) (sel == 1'b0) |-> (out == in0)
    );

    // The output should be 1 if sel is 1 and in1 is 1, otherwise 0.
    mux_output_check_2: assert property (
        @(posedge CLK) disable iff (!RSTn) (sel == 1'b1) |-> (out == in1)
    );

    // The output should be 0 if both sel is 0 and in0 is 0, otherwise 1.
    mux_output_check_3: assert property (
        @(posedge CLK) disable iff (!RSTn) (sel == 1'b0) && (in0 == 1'b0) |-> (out == 1'b0)
    );

    // The output should be 0 if both sel is 1 and in1 is 0, otherwise 1.
    mux_output_check_4: assert property (
        @(posedge CLK) disable iff (!RSTn) (sel == 1'b1) && (in1 == 1'b0) |-> (out == 1'b0)
    );

    // The output should be 0 if both sel is 0 and in0 is 1, otherwise 1.
    mux_output_check_5: assert property (
        @(posedge CLK) disable iff (!RSTn) (sel == 1'b0) && (in0 == 1'b1) |-> (out == 1'b1)
    );

    // The output should be 0 if both sel is 1 and in1 is 1, otherwise 1.
    mux_output_check_6: assert property (
        @(posedge CLK) disable iff (!RSTn) (sel == 1'b1) && (in1 == 1'b1) |-> (out == 1'b1)
    );

    // The output should be 0 if both sel is 0 and in0 is 0, otherwise 1.
    mux_output_check_7: assert property (
        @(posedge CLK) disable iff (!RSTn) (sel == 1'b0) && (in0 == 1'b0) |-> (out == 1'b0)
    );

    // The output should be 0 if both sel is 1 and in1 is 0, otherwise 1.
    mux_output_check_8: assert property (
        @(posedge CLK) disable iff (!RSTn) (sel == 1'b1) && (in1 == 1'b0) |-> (out == 1'b0)
    );

    // The output should be 0 if both sel is 0 and in0 is 1, otherwise 1.
    mux_output_check_9: assert property (
        @(posedge CLK) disable iff (!RSTn) (sel == 1'b0) && (in0 == 1'b1) |-> (out == 1'b1)
    );

    // The output should be 0 if both sel is 1 and in1 is 1, otherwise 1.
    mux_output_check_10: assert property (
        @(posedge CLK) disable iff (!RSTn) (sel == 1'b1) && (in1 == 1'b1) |-> (out == 1'b1)
    );
endmodule