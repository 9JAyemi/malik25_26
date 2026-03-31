```systemverilog
module add_sub_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic SUB,
    output logic [3:0] OUT
);
    // The logic is purely combinational, so we will use @(posedge clk) for assertions.

    // The output OUT is the result of either A + B or B - A based on the SUB signal.
    // When SUB is 0, OUT should be A + B.
    add_check: assert property (
        @(posedge clk) $rose(SUB) |-> (OUT == A + B)
    );
    // When SUB is 1, OUT should be B - A.
    sub_check: assert property (
        @(posedge clk) $fell(SUB) |-> (OUT == B - A)
    );
endmodule
```