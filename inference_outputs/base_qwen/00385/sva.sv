```systemverilog
module my_module_sva (
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2
);
    // NAND0 output is the NAND of A2 and A1
    nand0_out_check: assert property (
        @(posedge clk) disable iff (!RESETn) (nand0_out == !(A2 & A1))
    );

    // NAND1 output is the NAND of B2 and B1
    nand1_out_check: assert property (
        @(posedge clk) disable iff (!RESETn) (nand1_out == !(B2 & B1))
    );

    // AND0 output is the AND of NAND0_out and NAND1_out
    and0_out_check: assert property (
        @(posedge clk) disable iff (!RESETn) (and0_out_Y == (nand0_out & nand1_out))
    );

    // NOT0 output is the NOT of AND0_out
    not0_out_check: assert property (
        @(posedge clk) disable iff (!RESETn) (and1_out_Y == !(and0_out_Y))
    );

    // Y is the buffer of NOT0_out
    Y_check: assert property (
        @(posedge clk) disable iff (!RESETn) (Y == and1_out_Y)
    );
endmodule
```