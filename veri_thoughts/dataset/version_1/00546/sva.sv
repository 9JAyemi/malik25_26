module sky130_fd_sc_ms__clkdlyinv3sd3_sva (
    input logic A,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB,
    input logic clk,
    input logic Y
);

    // Y is the result of three inversions of A.
    check_y_matches_triple_inversion: assert property (
        @(posedge clk) Y == ~A
    );

    // A low produces Y high.
    check_output_high_when_input_low: assert property (
        @(posedge clk) !A |-> Y
    );

    // A high produces Y low.
    check_output_low_when_input_high: assert property (
        @(posedge clk) A |-> !Y
    );

    // Y always differs from A.
    check_output_is_logical_opposite: assert property (
        @(posedge clk) Y != A
    );

    // If A is stable across samples, Y is also stable.
    check_output_stable_when_input_stable: assert property (
        @(posedge clk) 1'b1 |=> ($stable(A) |-> $stable(Y))
    );

    // If A changes across samples, Y changes too.
    check_output_changes_with_input: assert property (
        @(posedge clk) 1'b1 |=> ($changed(A) |-> $changed(Y))
    );

    // Y can only change when A changes across samples.
    check_output_only_changes_with_input: assert property (
        @(posedge clk) 1'b1 |=> ($changed(Y) |-> $changed(A))
    );

    // A sampled rise yields a low sampled Y.
    check_output_low_on_input_rise: assert property (
        @(posedge clk) 1'b1 |=> ($rose(A) |-> !Y)
    );

    // A sampled fall yields a high sampled Y.
    check_output_high_on_input_fall: assert property (
        @(posedge clk) 1'b1 |=> ($fell(A) |-> Y)
    );

endmodule