module DFFSRAC_assertions (
    input logic CK,
    input logic D,
    input logic S,
    input logic R,
    input logic C,
    input logic Q,
    input logic QN
);

    // Clear has highest priority on the clock edge.
    check_clear_priority: assert property (
        @(posedge CK) C |=> (Q == 1'b0 && QN == 1'b1)
    );

    // Set drives the outputs when clear is not asserted.
    check_set_priority: assert property (
        @(posedge CK) (!C && S) |=> (Q == 1'b1 && QN == 1'b0)
    );

    // Reset drives the outputs when clear and set are not asserted.
    check_reset_priority: assert property (
        @(posedge CK) (!C && !S && R) |=> (Q == 1'b0 && QN == 1'b1)
    );

    // Data is captured when no control input is asserted.
    check_data_capture: assert property (
        @(posedge CK) (!C && !S && !R) |=> (Q == $past(D) && QN == ~$past(D))
    );

    // The two outputs remain complementary after each clock update.
    check_complementary_outputs: assert property (
        @(posedge CK) 1'b1 |=> (QN == ~Q)
    );

endmodule