```systemverilog
module signal_processor_sva(
    input logic [3:0] in,
    output logic [3:0] out
);
    // No clock or reset signals present in the RTL

    // Combinational logic: out is determined by the value of in
    // Check if out is correctly calculated for input less than 4
    comb_less_than_4: assert property (
        @(posedge clk) disable iff (!RESETn) (in < 4) |-> (out == in * 2)
    );

    // Check if out is correctly calculated for input between 4 and 7 (inclusive)
    comb_between_4_and_7: assert property (
        @(posedge clk) disable iff (!RESETn) (in >= 4 && in <= 7) |-> (out == in * in)
    );

    // Check if out is correctly calculated for input greater than 7
    comb_greater_than_7: assert property (
        @(posedge clk) disable iff (!RESETn) (in > 7) |-> (out == in / 2)
    );
endmodule
```