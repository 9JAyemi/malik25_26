```systemverilog
module mux_4to1_sva (
    input logic [1:0] S,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    output logic Y
);
    // Mux output should be one of the inputs based on the select signal S
    mux_output: assert property (
        @(posedge clk) disable iff (!rst_n) (S == 2'b00) |-> (Y == C)
    );
    mux_output: assert property (
        @(posedge clk) disable iff (!rst_n) (S == 2'b01) |-> (Y == D)
    );
    mux_output: assert property (
        @(posedge clk) disable iff (!rst_n) (S == 2'b10) |-> (Y == A)
    );
    mux_output: assert property (
        @(posedge clk) disable iff (!rst_n) (S == 2'b11) |-> (Y == B)
    );
endmodule
```