```systemverilog
module top_module_sva (
    input logic CLK,
    input logic CLR,
    input logic LD1,
    input logic LD2,
    input logic [3:0] D1,
    input logic [3:0] D2,
    output logic [3:0] sum
);
    wire [3:0] Q1, Q2; // Declare wires for shift register outputs

    shift_register sr1 (
        .D(D1),
        .LD(LD1),
        .CLK(CLK),
        .CLR(CLR),
        .Q(Q1) // Connect wire to shift_register output
    );

    shift_register sr2 (
        .D(Q1),
        .LD(LD2),
        .CLK(CLK),
        .CLR(CLR),
        .Q(Q2) // Connect wire to shift_register output
    );

    adder add (
        .A(Q1),
        .B(Q2),
        .sum(sum)
    );

    // Shift register 1: Q1 should be loaded with D1 when LD1 is high
    shift_reg1_load: assert property (
        @(posedge CLK) disable iff (!CLR) $rose(LD1) |-> (Q1 == D1)
    );

    // Shift register 1: Q1 should shift left when LD1 is low
    shift_reg1_shift: assert property (
        @(posedge CLK) disable iff (!CLR) $fell(LD1) |-> (Q1 == {Q1[2:0], Q1[3]})
    );

    // Shift register 2: Q2 should be loaded with Q1 when LD2 is high
    shift_reg2_load: assert property (
        @(posedge CLK) disable iff (!CLR) $rose(LD2) |-> (Q2 == Q1)
    );

    // Shift register 2: Q2 should shift left when LD2 is low
    shift_reg2_shift: assert property (
        @(posedge CLK) disable iff (!CLR) $fell(LD2) |-> (Q2 == {Q2[2:0], Q2[3]})
    );

    // Adder: sum should be the sum of Q1 and Q2
    adder_result: assert property (
        @(posedge CLK) disable iff (!CLR) (sum == Q1 + Q2)
    );

    // Clear signal should reset both shift registers to 0
    clear_signal: assert property (
        @(posedge CLK) !CLR |-> (Q1 == 4'b0000) && (Q2 == 4'b0000)
    );

endmodule
```