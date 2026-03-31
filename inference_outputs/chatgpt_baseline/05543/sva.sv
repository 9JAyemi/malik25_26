module sky130_fd_sc_ls__clkdlyinv3sd1_sva (
    input logic clk,
    input logic Y,
    input logic A
);

    // Output always equals the inversion of the input.
    check_inversion_function: assert property (
        @(posedge clk) Y === ~A
    );

    // A low input drives Y high.
    check_low_input_high_output: assert property (
        @(posedge clk) (A === 1'b0) |-> (Y === 1'b1)
    );

    // A high input drives Y low.
    check_high_input_low_output: assert property (
        @(posedge clk) (A === 1'b1) |-> (Y === 1'b0)
    );

    // A known input produces a known output.
    check_known_input_known_output: assert property (
        @(posedge clk) !$isunknown(A) |-> !$isunknown(Y)
    );

    // A sampled input change causes a sampled output change.
    check_output_changes_with_input: assert property (
        @(posedge clk)
        (!$isunknown(A) && !$isunknown($past(A)) &&
         !$isunknown(Y) && !$isunknown($past(Y)) &&
         (A != $past(A))) |-> (Y != $past(Y))
    );

    // A sampled stable input keeps the sampled output stable.
    check_output_stable_with_input: assert property (
        @(posedge clk)
        (!$isunknown(A) && !$isunknown($past(A)) &&
         !$isunknown(Y) && !$isunknown($past(Y)) &&
         (A == $past(A))) |-> (Y == $past(Y))
    );

endmodule