```systemverilog
module binary_adder_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic CTRL,
    output logic [3:0] C
);
    // Sequential logic assertion
    // C should be the sum of A and B when CTRL is 0
    sequential_addition: assert property (
        @(posedge CLK) disable iff (!RESETn) (CTRL == 0) |-> (C == A + B)
    );
    // Sequential logic assertion
    // C should be the sum of the upper bits of A and B when CTRL is 1
    sequential_shifted_addition: assert property (
        @(posedge CLK) disable iff (!RESETn) (CTRL == 1) |-> (C == {1'b0, A[3:1]} + {1'b0, B[3:1]})
    );
endmodule
```