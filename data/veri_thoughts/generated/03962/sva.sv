module busm_sva (
    input logic clk,
    input logic [3:0] iB,
    input logic [3:0] oB
);

    // Output is the input value captured on the previous clock edge.
    check_output_delays_input: assert property (
        @(posedge clk) !$initstate |-> (oB == $past(iB))
    );

    // A changed input is not reflected until the following cycle.
    check_one_cycle_latency_on_change: assert property (
        @(posedge clk) (!$initstate && (iB != $past(iB))) |-> ((oB == $past(iB)) && (oB != iB))
    );

    // If the input is unchanged across two cycles, the output matches that value.
    check_output_matches_stable_input: assert property (
        @(posedge clk) (!$initstate && (iB == $past(iB))) |-> (oB == iB)
    );

endmodule