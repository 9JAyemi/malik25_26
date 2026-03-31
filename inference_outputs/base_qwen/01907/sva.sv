```systemverilog
module and_module_sva (
    input logic clk,
    input logic rst_n,
    input logic [7:0] i_bus1,
    input logic [7:0] i_bus2,
    output wire [7:0] o_bus
);
    // Combinational logic: o_bus is the result of i_bus1 AND i_bus2
    // This assertion checks that o_bus is correctly calculated at each clock edge
    comb_logic: assert property (
        @(posedge clk) disable iff (!rst_n) (o_bus == (i_bus1 & i_bus2))
    );
endmodule
```