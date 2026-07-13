module bit_concatenator_sva (
    input logic in1,
    input logic in2,
    input logic in3,
    input logic in4,
    input logic ctrl,
    input logic [3:0] out
);

    // Expected combinational result of the DUT
    function automatic logic [3:0] expected_out (
        input logic i1, input logic i2, input logic i3, input logic i4, input logic c
    );
        expected_out = { (c ? ~i1 : i1), (c ? ~i2 : i2), i3, i4 };
    endfunction

    // On posedge of in1, out matches the defined mapping after delta cycle.
    check_out_mapping_pos_in1: assert property (
        @(posedge in1) ##0 (out == expected_out(in1, in2, in3, in4, ctrl))
    );

    // On negedge of in1, out matches the defined mapping after delta cycle.
    check_out_mapping_neg_in1: assert property (
        @(negedge in1) ##0 (out == expected_out(in1, in2, in3, in4, ctrl))
    );

    // On posedge of in2, out matches the defined mapping after delta cycle.
    check_out_mapping_pos_in2: assert property (
        @(posedge in2) ##0 (out == expected_out(in1, in2, in3, in4, ctrl))
    );

    // On negedge of in2, out matches the defined mapping after delta cycle.
    check_out_mapping_neg_in2: assert property (
        @(negedge in2) ##0 (out == expected_out(in1, in2, in3, in4, ctrl))
    );

    // On posedge of in3, out matches the defined mapping after delta cycle.
    check_out_mapping_pos_in3: assert property (
        @(posedge in3) ##0 (out == expected_out(in1, in2, in3, in4, ctrl))
    );

    // On negedge of in3, out matches the defined mapping after delta cycle.
    check_out_mapping_neg_in3: assert property (
        @(negedge in3) ##0 (out == expected_out(in1, in2, in3, in4, ctrl))
    );

    // On posedge of in4, out matches the defined mapping after delta cycle.
    check_out_mapping_pos_in4: assert property (
        @(posedge in4) ##0 (out == expected_out(in1, in2, in3, in4, ctrl))
    );

    // On negedge of in4, out matches the defined mapping after delta cycle.
    check_out_mapping_neg_in4: assert property (
        @(negedge in4) ##0 (out == expected_out(in1, in2, in3, in4, ctrl))
    );

    // On posedge of ctrl, out matches the defined mapping after delta cycle.
    check_out_mapping_pos_ctrl: assert property (
        @(posedge ctrl) ##0 (out == expected_out(in1, in2, in3, in4, ctrl))
    );

    // On negedge of ctrl, out matches the defined mapping after delta cycle.
    check_out_mapping_neg_ctrl: assert property (
        @(negedge ctrl) ##0 (out == expected_out(in1, in2, in3, in4, ctrl))
    );

endmodule