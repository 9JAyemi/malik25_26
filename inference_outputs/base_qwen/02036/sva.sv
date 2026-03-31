```systemverilog
module mux_2to1_enable_sva (
    input logic A,
    input logic B,
    input logic EN,
    output logic Y
);
    // EN can only transition from LOW to HIGH when A and B are equal.
    mux_enable_1: assert property (
        @(posedge clk) disable iff (!RESETn) $rose(EN) |-> (A == B)
    );
    // Y should always be equal to A when EN is LOW.
    mux_enable_2: assert property (
        @(posedge clk) disable iff (!RESETn) (EN == 1'b0) |-> (Y == A)
    );
    // Y should always be equal to B when EN is HIGH.
    mux_enable_3: assert property (
        @(posedge clk) disable iff (!RESETn) (EN == 1'b1) |-> (Y == B)
    );
endmodule
```