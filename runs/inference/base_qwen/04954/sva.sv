module pipelined_adder_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    output logic [3:0] OUT
);
    // Sequential logic: sum_reg1, sum_reg2, sum_reg3 are updated on each clock edge
    // Ensure that sum_reg3 is updated with the correct value after two clock cycles
    pipeline_update: assert property (
        @(posedge clk) $rose(OUT) |-> (OUT == A + B)
    );
    // Combinational logic: OUT is assigned the value of sum_reg3
    // Ensure that OUT is updated with the value of sum_reg3 on the current clock edge
    combinational_update: assert property (
        @(posedge clk) $rose(OUT) |-> (OUT == sum_reg3)
    );
endmodule