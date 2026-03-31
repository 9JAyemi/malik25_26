```systemverilog
module subtractor_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    output logic [3:0] Y
);
    // Combinational logic, so use @(posedge clk)
    // Y is assigned the result of A - B
    comb_logic: assert property (
        @(posedge clk) disable iff (!reset_n) Y == A - B
    );
endmodule
```