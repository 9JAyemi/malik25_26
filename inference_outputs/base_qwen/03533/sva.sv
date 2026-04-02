module my_module_sva (
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic B2,
    output logic X
);
    // A2_A3 is assigned the result of A2 AND NOT A3
    assign_sva_1: assert property (
        @(posedge clk) disable iff (!reset_n) A2_A3 == (A2 & ~A3)
    );

    // X is assigned the result of (A1 OR A2_A3) AND B1
    assign_sva_2: assert property (
        @(posedge clk) disable iff (!reset_n) X == ((A1 | A2_A3) & B1)
    );
endmodule