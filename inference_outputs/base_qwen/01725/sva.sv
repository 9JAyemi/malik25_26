```systemverilog
module mm_sva (
    input logic clk,
    input logic rst_n,
    input logic [31:0] addr,
    output logic [7:0] mod,
    output logic [31:0] eff_addr
);
    // Combinational logic, but still use clocked assertions
    // mod is calculated based on addr[31:20]
    mod_calc: assert property (
        @(posedge clk) disable iff (!rst_n) (mod == (addr[31:20] == 12'h000) ? 0 : 
                                             (addr[31:24] == 8'h10) ? 1 : 
                                             (addr[31:20] == 12'hf00) ? 2 : 
                                             (addr[31:20] == 12'hf01) ? 3 : 
                                             (addr[31:20] == 12'hf02) ? 4 : 
                                             (addr[31:20] == 12'hf03) ? 5 : 
                                             (addr[31:20] == 12'hf04) ? 6 : 
                                             (addr[31:20] == 12'hf05) ? 7 : 
                                             (addr[31:20] == 12'hf06) ? 8 : 
                                             (addr[31:20] == 12'hf07) ? 10 : 
                                             (addr[31:20] == 12'hf08) ? 11 : 
                                             (addr[31:20] == 12'hf0a) ? 9 : 
                                             0)
    );

    // eff_addr is calculated based on mod and addr
    eff_addr_calc: assert property (
        @(posedge clk) disable iff (!rst_n) (eff_addr == (mod == 8'h01) ? {8'h00, addr[23:0]} : {12'h000, addr[19:0]})
    );
endmodule
```