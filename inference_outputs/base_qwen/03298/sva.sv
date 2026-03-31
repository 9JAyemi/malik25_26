```systemverilog
module logic_gate_sva (
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1,
    input logic D1,
    output logic X
);
    // Check if X is 1 when either condition1 or condition2 is true
    condition1_check: assert property (
        @(posedge clk) disable iff (!reset_n) (condition1 || condition2) |-> (X == 1)
    );

    // Check if X is 0 when condition3 is true
    condition3_check: assert property (
        @(posedge clk) disable iff (!reset_n) (condition3) |-> (X == 0)
    );

    // Check if X is 0 when neither condition1 nor condition2 is true and condition3 is false
    default_check: assert property (
        @(posedge clk) disable iff (!reset_n) !(condition1 || condition2 || condition3) |-> (X == 0)
    );
endmodule
```