```systemverilog
module arithmetic_module_sva (
    input logic clk,
    input logic rst_n,
    input logic Boo_ba1,
    input logic Boo_ba2,
    input logic b,
    input logic Boo_ba3,
    input logic c,
    output logic [3:0] f4_dotnamed
);

    // Sequential logic in SubA
    // f1_dotnamed is assigned based on Boo_ba1
    sequential_suba: assert property (
        @(posedge clk) disable iff (!rst_n) f1_dotnamed == Boo_ba1 << 1
    );

    // Sequential logic in SubB
    // f2_dotnamed is assigned based on Boo_ba2 and b
    sequential_subb: assert property (
        @(posedge clk) disable iff (!rst_n) f2_dotnamed == Boo_ba2 + b
    );

    // Sequential logic in SubC
    // f3_dotnamed is assigned based on Boo_ba3 and c
    sequential_subc: assert property (
        @(posedge clk) disable iff (!rst_n) f3_dotnamed == Boo_ba3 - c
    );

    // Combinational logic in arithmetic_module
    // f4_dotnamed is the sum of f1_dotnamed, f2_dotnamed, and f3_dotnamed
    combinational_logic: assert property (
        @(posedge clk) disable iff (!rst_n) f4_dotnamed == f1_dotnamed + f2_dotnamed + f3_dotnamed
    );

    // Reset behavior
    // At reset, all outputs should be zero
    reset_behavior: assert property (
        @(posedge clk) disable iff (!rst_n) f4_dotnamed == 4'b0000
    );

endmodule
```