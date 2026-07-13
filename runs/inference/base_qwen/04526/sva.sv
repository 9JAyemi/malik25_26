module my_module_sva (
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1,
    output logic Y
);
    // Sequential logic behavior
    // Y is the output of a buffer, so it should always be equal to the input of the buffer
    buffer_output: assert property (
        @(posedge clk) disable iff (!RESETn) Y == not0_out
    );

    // Combinational logic behavior
    // The output of the buffer is the output of the not gate
    not_output: assert property (
        @(posedge clk) disable iff (!RESETn) not0_out == ~and0_out
    );

    // The output of the not gate is the output of the and gate
    and_output: assert property (
        @(posedge clk) disable iff (!RESETn) and0_out == (or0_out & B1 & C1)
    );

    // The output of the or gate is the OR of A1 and A2
    or_output: assert property (
        @(posedge clk) disable iff (!RESETn) or0_out == (A1 | A2)
    );
endmodule