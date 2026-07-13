module my_module_sva (
    input logic CLK,
    input logic RESETn,
    input logic A,
    input logic TE_B,
    output logic Z
);
    // Combinational logic behavior: Z = TE_B ? 1'b1 : A
    // This behavior is always active, so we use @(posedge CLK) to clock the assertion
    comb_logic: assert property (
        @(posedge CLK) disable iff (!RESETn) (Z == (TE_B ? 1'b1 : A))
    );
endmodule