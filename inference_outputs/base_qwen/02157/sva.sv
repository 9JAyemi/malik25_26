```systemverilog
module custom_module_sva (
    input logic A1,
    input logic A2,
    input logic B1,
    output logic X
);
    // Combinational logic: X is the AND of A1 and A2, and B1
    // This is a clocked assertion to ensure the behavior is met at the clock edge
    comb_logic: assert property (
        @(posedge clk) disable iff (!reset_n) (X == (A1 & A2 & B1))
    ) else $error("Combinational logic error: X is not equal to A1 & A2 & B1");

    // Ensure that the supply signals are properly defined
    // This is a clocked assertion to ensure the behavior is met at the clock edge
    supply_assertion: assert property (
        @(posedge clk) disable iff (!reset_n) (VPWR == 1'b1 && VGND == 1'b0 && VPB == 1'b1 && VNB == 1'b0)
    ) else $error("Supply signal assertion error: VPWR, VGND, VPB, or VNB is not correctly defined");

    // Ensure that the base cell is instantiated correctly
    // This is a clocked assertion to ensure the behavior is met at the clock edge
    base_cell_assertion: assert property (
        @(posedge clk) disable iff (!reset_n) (X == base.X)
    ) else $error("Base cell instantiation error: X is not equal to base.X");
endmodule
```