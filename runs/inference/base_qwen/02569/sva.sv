module and_gate_sva (
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1,
    input logic D1
);
    // Sequential logic is not present, so all logic is combinational.
    // No clock or reset signals are present in the RTL.

    // Check that Y is the result of the nested AND operations.
    check_and_result: assert property (
        @(posedge clk) disable iff (!RESETn) (Y == (A1 && A2 && B1 && C1 && D1))
    );
endmodule