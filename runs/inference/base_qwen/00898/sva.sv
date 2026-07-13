module adder_subtractor_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic SUB,
    output logic [3:0] SUM
);
    // Combinational logic: SUM is calculated based on A, B, and SUB
    // SUM = A + B if SUB is 0, SUM = A - B if SUB is 1
    // B_comp is the two's complement of B
    wire [3:0] B_comp;
    assign B_comp = ~B + 1;

    // Property to check the correct calculation of SUM
    property p_sum_calculation;
        @(posedge CLK) disable iff (!RESETn) (SUB == 1'b0) |-> (SUM == A + B);
    endproperty
    assert property (p_sum_calculation) else $error("SUM calculation is incorrect when SUB is 0");

    property p_sum_subtraction;
        @(posedge CLK) disable iff (!RESETn) (SUB == 1'b1) |-> (SUM == A + B_comp);
    endproperty
    assert property (p_sum_subtraction) else $error("SUM calculation is incorrect when SUB is 1");

endmodule